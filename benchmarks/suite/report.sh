#!/usr/bin/env bash
# Report generation reads retained samples only; it never executes a benchmark.

session_measurements() {
    local directory=$1 output=$2 state=$1/session.json task file hash count fragment fragments metadata
    [[ -f $state ]] && jq -e '.finished_utc!=null and (.completed|length)==((.plan.jobs|length)*.plan.profile.passes)' "$state" >/dev/null || \
        { fail 'Session is incomplete; resume it before reporting'; return 1; }
    [[ -f $directory/corpus.json ]] && [[ $(digest "$directory/corpus.json") == "$(jq -r .corpus_sha256 "$state")" ]] || { fail 'Shared corpus changed'; return 1; }
    fragments=$output.parts.jsonl
    : >"$fragments"
    count=$(jq -r .plan.profile.samples "$state")
    while IFS= read -r task; do
        file=$(jq -r .file <<<"$task"); hash=$(jq -r .sha256 <<<"$task")
        [[ $file == "${file##*/}" && $file != *..* && -f $directory/$file ]] || { fail 'Invalid raw report path'; return 1; }
        [[ $(digest "$directory/$file") == "$hash" ]] || { fail 'Recorded raw data changed'; return 1; }
        validate_native_report "$directory/$file" "$count"
        jq -c --arg configuration "$(jq -r .configuration <<<"$task")" --argjson pass "$(jq .pass <<<"$task")" '
          .measurements[] | {configuration:$configuration,operation:.name,pass:{pass:$pass,
            iterations:.calibrated_iterations,work_items_per_iteration,
            elapsed_ns:[.samples[].elapsed_ns],sample_order:[.samples[].order]}}
        ' "$directory/$file" >>"$fragments"
    done < <(jq -c '.completed[]' "$state")
    jq -n --slurpfile state "$state" --slurpfile parts "$fragments" '
      $state[0] as $s |
      ($s.builds.jobs|to_entries|map({key:.key,value:{configuration:.value.configuration,
        rustflags:.value.rustflags,binary_sha256:.value.binary_sha256,build_profile:.value.profile,
        compiled:.value.build.build,experimental_adapter:.value.build.build.experimental_adapter,
        c_build_environment:.value.cflags,resolved_cargo_features:.value.resolved_cargo_features}})|from_entries) as $configs |
      {schema_version:2,role:"Linux native benchmark session",source_revision:$s.source.revision,
       measurement_source_commit:null,source_tracked_changes:$s.source.tracked_changes,source_files_sha256:$s.source.files,
       reference_revision:([$configs[].resolved_cargo_features[]|select(.name=="lean_sphincs")|.source|split("#")[-1]]|unique|if length==1 then .[0] else error("Inconsistent reference revision") end),
       corpus_sha256:$s.corpus_sha256,cpu:$s.machine.processors[0],rustc:$s.builds.rustc,
       sampling:{samples_per_case:$s.plan.profile.samples,passes:$s.plan.profile.passes,
         positive_fixtures:($s.plan.profile.extra_cases+3),batch_target_ms:$s.plan.profile.sample_ms,
         warmup_ms:$s.plan.profile.warmup_ms,shuffle_seed:$s.plan.seed,outliers_removed:0},configurations:$configs,
       measurements:($parts|sort_by(.configuration,.operation)|group_by([.configuration,.operation])|
         map({configuration:.[0].configuration,operation:.[0].operation,passes:(map(.pass)|sort_by(.pass))}))}
    ' >"$output"
    rm -f -- "$fragments"
}

render_native_markdown() {
    local data=$1 summary=$2 destination=$3 reference=$4 mode op label unit divisor own upstream adapter
    local cpu compiler llvm backend_count
    cpu=$(jq -r '.cpu.Name|gsub("^ +| +$";"")' "$data"); compiler=$(jq -r '.rustc|split("\n")[0]' "$data")
    llvm=$(jq -r '.rustc|split("\n")[]|select(startswith("LLVM version:"))' "$data")
    mode=macro; jq -e 'any(.[];.name|startswith("direct/"))' "$summary" >/dev/null && mode=direct
    {
        printf '# Native benchmark results\n\nCPU: %s.\n\nCompiler: %s; %s.\n\n' "$cpu" "$compiler" "$llvm"
        printf 'Medians of all %s samples per case over %s passes. All samples retained.\n\n' \
            "$(( $(jq -r .sampling.samples_per_case "$data") * $(jq -r .sampling.passes "$data") ))" "$(jq -r .sampling.passes "$data")"
        if [[ $mode == direct ]]; then
            printf 'Direct native APIs. leanVM receives parsed verification inputs; lean-sphincs borrows encoded bytes.\nSigning and key generation return native results without added serialization.\n\n'
        else
            printf 'Wire-format API boundaries, including the format conversions in the recorded harness.\n\n'
        fi
        printf 'The Keccak column selects Alloy hashing; leanVM uses its own CPU-selected implementation.\nFaster = `(leanVM time / lean-sphincs time - 1) * 100%%`. Negative means slower.\n\n'
        printf 'leanVM revision: `%s`. Exact build flags and features are in the measurement JSON.\n\n' "$(jq -r .reference_revision "$data")"
        for op in verify sign key_gen; do
            case "$op" in verify) label=Verification;unit='µs';divisor=1000;; sign) label=Signing;unit=ms;divisor=1000000;; key_gen) label='Key generation';unit=ms;divisor=1000000;; esac
            if [[ $mode == direct ]]; then own=direct/lean-sphincs/$op; upstream=direct/leanVM/$op
            else
                local name=$op; [[ $op != verify ]] || name=verify_wire
                own=macro/native/$name/mixed; upstream=macro/reference/$name/mixed
            fi
            jq -e --arg own "$own" 'any(.[];.name==$own)' "$summary" >/dev/null || continue
            printf '## %s\n\n| Compiler target | Alloy Keccak | LLVM SLP | lean-sphincs (%s) |' "$label" "$unit"
            if [[ $reference == true ]]; then printf ' leanVM, unmodified (%s) | Faster than leanVM |' "$unit"; fi
            printf '\n| --- | --- | --- | ---: |'; if [[ $reference == true ]]; then printf ' ---: | ---: |'; fi; printf '\n'
            jq -r --slurpfile rows "$summary" --arg own "$own" --arg upstream "$upstream" '
              ($rows[0]|map({key:(.configuration+"/"+.name),value:.median_ns})|from_entries) as $v |
              .configurations|to_entries|sort_by(.value.configuration.target.id,.value.configuration.keccak,.key)[] |
              .key as $id|.value as $b|$b.configuration as $c|
              select($v[$id+"/"+$own]!=null) |
              [({baseline:"SSE2",v2:"SSE4.2",v3:"AVX2",v4:"AVX-512",native:"native"}[$c.target.id]//$c.target.id),
               ({portable:"RustCrypto",tiny:"tiny-keccak",assembly:"asm-keccak"}[$c.keccak]//$c.keccak),
               (if ($b.rustflags//[]|index("no-vectorize-slp")) then "disabled" else "enabled" end),
               $v[$id+"/"+$own],($v[$id+"/"+$upstream]//"-")] | @tsv
            ' "$data" | awk -F '\t' -v divisor="$divisor" -v reference="$reference" '{
                printf "| %s | %s | %s | %.2f |",$1,$2,$3,$4/divisor
                if(reference=="true"){
                    if($5=="-")printf " - | - |";else printf " %.2f | %+.1f%% |",$5/divisor,($5/$4-1)*100
                }
                print ""
            }'
            printf '\n'
        done
        if jq -e 'any(.[];.name=="macro/evm2/ecrecover")' "$summary" >/dev/null; then
            printf '## evm2 ecrecover\n\n| Compiler target | Address Keccak | LLVM SLP | Recovery provider | Time (µs) |\n| --- | --- | --- | --- | ---: |\n'
            jq -r --slurpfile rows "$summary" '
              ($rows[0]|map(select(.name=="macro/evm2/ecrecover")|{key:.configuration,value:.median_ns})|from_entries) as $v |
              .configurations|to_entries|sort_by(.value.configuration.target.id,.value.configuration.keccak,.key)[] |
              .key as $id|.value as $b|$b.configuration as $c|select($v[$id]!=null)|
              [({baseline:"SSE2",v2:"SSE4.2",v3:"AVX2",v4:"AVX-512",native:"native"}[$c.target.id]//$c.target.id),
               ({portable:"RustCrypto",tiny:"tiny-keccak",assembly:"asm-keccak"}[$c.keccak]//$c.keccak),
               (if ($b.rustflags//[]|index("no-vectorize-slp")) then "disabled" else "enabled" end),$c.ecrecover,$v[$id]]|@tsv
            ' "$data" | awk -F '\t' '{printf "| %s | %s | %s | %s | %.2f |\n",$1,$2,$3,$4,$5/1000}'
            printf '\n'
        fi
        if jq -e 'any(.[];.name|startswith("macro/batched/"))' "$summary" >/dev/null; then
            printf '## Local batching experiment\n\nThese explicitly selected cases use the local adapter and are not unmodified leanVM.\nSee `summary.json` for every adapter case; they are excluded from the stock tables above.\n\n'
        fi
        printf 'All rejection and isolated hash cases, distributions and block-bootstrap intervals remain in `summary.json` and `summary.csv`.\n'
    } >"$destination"
}

report_native() {
    local session=$1 measurements=$2 resamples=$3 reference=$4 output data temporary
    [[ -n $session && -z $measurements || -z $session && -n $measurements ]] || { fail 'Report requires exactly one of --session or --measurements'; return 1; }
    if [[ -n $session ]]; then
        output=$(realpath -- "$session"); data=$output/measurements.json
        session_measurements "$output" "$data"
    else
        [[ -f $measurements ]] || { fail 'Measurement JSON does not exist'; return 1; }
        data=$(realpath -- "$measurements"); output=$BENCH_RESULTS/published/$(basename -- "${data%.json}")
        mkdir -p -- "$output"
    fi
    temporary=$output/normalized.tsv
    jq -er -f "$HERE/suite/normalize.jq" "$data" >"$temporary"
    awk -v resamples="$resamples" -v seed=20261115 -v block=10 -f "$HERE/suite/stats.awk" "$temporary" |
        jq -s 'sort_by(.configuration,.name)' >"$output/summary.json"
    rm -f -- "$temporary"
    jq -r '(["configuration","name","samples","passes","median_ns","p05_ns","p95_ns","p99_ns","mean_ns","stdev_ns","pass_median_spread_percent"]|@csv),
      (.[]|[.configuration,.name,.samples,.passes,.median_ns,.p05_ns,.p95_ns,.p99_ns,.mean_ns,.stdev_ns,.pass_median_spread_percent]|@csv)' \
      "$output/summary.json" >"$output/summary.csv"
    render_native_markdown "$data" "$output/summary.json" "$output/README-benchmarks.md" "$reference"
    printf 'Created %s from retained samples; no benchmarks ran.\n' "$output/README-benchmarks.md"
}
