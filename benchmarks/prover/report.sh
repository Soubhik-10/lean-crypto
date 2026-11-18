#!/usr/bin/env bash
# Curate stock CLI reports and render comparisons without invoking a prover.
export_prover_session() {
    local directory=$1 output=$2 state=$1/session.json item file stem recorded metrics parts=$2.parts.jsonl
    jq -e '.complete==true and (.completed|length)==(.plan.jobs|length)' "$state" >/dev/null || { fail 'Prover session is incomplete'; return 1; }
    : >"$parts"
    while IFS= read -r item; do
        file=$(jq -r .file <<<"$item")
        [[ $file != /* && $file != *..* && $file == */execution.json ]] || { fail 'Unsafe prover report path'; return 1; }
        stem=$directory/${file%/execution.json}
        [[ $(digest "$directory/$file") == "$(jq -r .sha256 <<<"$item")" ]] || { fail 'Prover execution record changed'; return 1; }
        [[ $(digest "$stem/cli.stdout.log") == "$(jq -r .stdout_sha256 <<<"$item")" && \
           $(digest "$stem/cli.stderr.log") == "$(jq -r .stderr_sha256 <<<"$item")" ]] || { fail 'Prover logs changed'; return 1; }
        metrics=$(jq -n --rawfile stdout "$stem/cli.stdout.log" --rawfile stderr "$stem/cli.stderr.log" '{stdout:$stdout,stderr:$stderr}' |
            jq --argjson repeat "$(jq .plan.repeat "$state")" -f "$PROVER_HERE/parse.jq")
        jq -e --argjson metrics "$metrics" '.returncode==0 and .metrics==$metrics' "$directory/$file" >/dev/null || { fail 'Stored metrics disagree with stock logs'; return 1; }
        jq -c --rawfile stdout "$stem/cli.stdout.log" --rawfile stderr "$stem/cli.stderr.log" \
            '{revision:.job.revision,sha:.job.sha,prover:.job.prover,workers:.job.threads,cpu_allocation:.job.cpus,
              workload:.job.workload,command:(["leanvm"]+.command[1:]),binary_sha256,exit_code:.returncode,metrics,
              raw_stdout:$stdout,raw_stderr:$stderr}' "$directory/$file" >>"$parts"
    done < <(jq -c '.completed[]' "$state")
    jq -n --slurpfile state "$state" --slurpfile reports "$parts" '
      $state[0] as $s|{schema_version:1,role:"Unmodified upstream leanVM CLI proving comparison",
      repository:"https://github.com/leanEthereum/leanVM",cpu:$s.machine.processors[0],
      revisions:($s.plan.jobs|map({key:.revision,value:.sha})|from_entries),
      sampling:{measured_proving_passes:$s.plan.repeat,discarded_upstream_warmup_passes:1,per_pass_precision_s:0.001,outliers_removed:0},
      parameters:{rustflags:$s.plan.rustflags,log_inverse_rate:$s.plan.log_inverse_rate},
      fixture_caches_sha256:$s.fixture_cache_sha256,
      builds:($s.builds|with_entries(.value|={sha,binary_sha256,rustc,rustflags,cargo_lock_sha256,cargo_features})),
      measurements:($reports|sort_by(.revision,.workload,.workers,.prover))}' >"$output"
    rm -f -- "$parts"
}

report_provers() {
    local session=$1 measurements=$2 data output rows compiler
    [[ -n $session && -z $measurements || -z $session && -n $measurements ]] || { fail 'Choose exactly one --session or --measurements'; return 1; }
    if [[ -n $session ]]; then
        output=$(realpath -- "$session"); data=$output/measurements.json
        export_prover_session "$output" "$data"
    else
        [[ -f $measurements ]] || { fail 'Measurement JSON does not exist'; return 1; }
        data=$(realpath -- "$measurements"); output=$PROVER_RESULTS/published/$(basename -- "${data%.json}")
        mkdir -p -- "$output"
    fi
    compiler=$(jq -r '.builds|to_entries[0].value.rustc//"Compiler not reported"' "$data")
    rows=$output/summary.json
    jq -e '. as $d|(.measurements|length)>0 and
      ([.measurements[]|[.revision,.workload,.workers,.prover]]|length==(unique|length)) and
      all(.measurements[]; .exit_code==0 and (.metrics.proof_samples_s|length)==$d.sampling.measured_proving_passes and
        all(.metrics.proof_samples_s[];type=="number" and .>0) and .metrics.reported_verify_mean_ms>0 and
        .metrics.reported_proof_size_kib>0)' "$data" >/dev/null || { fail 'Incomplete or invalid proving measurements'; return 1; }
    jq '[.measurements[]|{revision,sha,prover,workers,workload,
      workload_label:({"sphincs-16":"16 leanSPHINCS signatures","sphincs-128":"128 leanSPHINCS signatures",
        "xmss-128":"128 leanXMSS signatures","xmss-1000":"1,000 leanXMSS signatures","mixed-64":"32 leanSPHINCS + 32 leanXMSS",
        "recursion-sphincs-2x16":"Recursive: 2 x 16 leanSPHINCS","recursion-xmss-8x128":"Recursive: 8 x 128 leanXMSS"}[.workload]//.workload),
      proving_mean_s:(.metrics.proof_samples_s|add/length),verification_mean_ms:.metrics.reported_verify_mean_ms,
      proof_kib:.metrics.reported_proof_size_kib,peak_rss_gib:.metrics.reported_peak_rss_gib}]' "$data" >"$rows"
    {
        printf '# leanVM proving results\n\nCPU: %s.\n\n' "$(jq -r '.cpu.Name//.cpu.model//"CPU not reported"|gsub("^ +| +$";"")' "$data")"
        printf 'Compiler: %s; %s.\n\n' "$(printf '%s\n' "$compiler" | awk '/^rustc /{print "Rust "$2;exit}')" \
            "$(printf '%s\n' "$compiler" | awk '/^LLVM version:/{print "LLVM "$3;exit}')"
        printf 'Unmodified upstream `leanvm-cli`. Both provers are compiled in with default CLI\ndependencies, including `aggregation/signers-cache`; `--prover` selects the implementation.\n\n'
        jq -r '.revisions|to_entries[]|"- "+.key+": `"+.value+"`"' "$data"
        printf '\nProving times are means of all %s retained passes after one stock warmup.\nThe CLI prints passes to millisecond precision. Faster = `(baseline / compared - 1) * 100%%`.\nRecursive timings cover the parent aggregate; child proof construction is excluded.\nPeak RSS is the parent process lifetime peak and excludes child-process memory.\n\n' \
            "$(jq -r .sampling.measured_proving_passes "$data")"
        if jq -e 'any(.[];.revision=="current" and .prover=="stable") and any(.[];.revision=="current" and .prover=="experimental")' "$rows" >/dev/null; then
            printf '## Current stable versus experimental\n\n| Workload | Workers | Stable (s) | Experimental (s) | Experimental faster |\n| --- | ---: | ---: | ---: | ---: |\n'
            jq -r '[.[]|select(.revision=="current")]|group_by([.workload,.workers])[]|
              (map(select(.prover=="stable"))[0]) as $a|(map(select(.prover=="experimental"))[0]) as $b|
              select($a!=null and $b!=null)|[$a.workload_label,$a.workers,$a.proving_mean_s,$b.proving_mean_s]|@tsv' "$rows" |
                awk -F '\t' '{printf "| %s | %s | %.4f | %.4f | %+.1f%% |\n",$1,$2,$3,$4,($3/$4-1)*100}'
            printf '\n'
        fi
        if jq -e 'any(.[];.revision=="previous") and any(.[];.revision=="current")' "$rows" >/dev/null; then
            printf '## Previous versus current\n\n| Workload | Workers | Prover | Previous (s) | Current (s) | Current faster |\n| --- | ---: | --- | ---: | ---: | ---: |\n'
            jq -r 'group_by([.workload,.workers,.prover])[]|
              (map(select(.revision=="previous"))[0]) as $a|(map(select(.revision=="current"))[0]) as $b|
              select($a!=null and $b!=null)|[$a.workload_label,$a.workers,$a.prover,$a.proving_mean_s,$b.proving_mean_s]|@tsv' "$rows" |
                awk -F '\t' '{printf "| %s | %s | %s | %.4f | %.4f | %+.1f%% |\n",$1,$2,$3,$4,$5,($4/$5-1)*100}'
            printf '\n'
        fi
        printf '## Complete measurements\n\n| Revision | Workload | Workers | Prover | Proving (s) | Verification (ms) | Proof (KiB) | Peak RSS (GiB) |\n| --- | --- | ---: | --- | ---: | ---: | ---: | ---: |\n'
        jq -r '.[]|[.revision,.workload_label,.workers,.prover,.proving_mean_s,.verification_mean_ms,.proof_kib,.peak_rss_gib]|@tsv' "$rows" |
            awk -F '\t' '{printf "| %s | %s | %s | %s | %.4f | %.3f | %.1f | %.3f |\n",$1,$2,$3,$4,$5,$6,$7,$8}'
    } >"$output/README-benchmarks.md"
    printf 'Created %s from retained CLI reports; no prover ran.\n' "$output/README-benchmarks.md"
}
