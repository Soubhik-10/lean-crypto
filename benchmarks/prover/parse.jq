def number($s;$pattern): $s|capture($pattern).v|tonumber;
. as $raw |
([$raw.stderr|match("passes\\s*:\\s*(?<values>[^\\n]+)";"g")|.captures[0].string]|last) as $line |
[$line|scan("[0-9]+(?:\\.[0-9]+)?(?= s)")|tonumber] as $samples |
if ($samples|length)!=$repeat or any($samples[];.<=0) then error("Incomplete stock CLI pass report") else
{proof_samples_s:$samples,sample_precision_s:0.001,
 reported_proving_mean_s:number($raw.stdout;"proving time\\s*:\\s*(?<v>[0-9.]+) s"),
 reported_verify_mean_ms:number($raw.stdout;"verifying\\s*:\\s*(?<v>[0-9.]+) ms"),
 reported_proof_size_kib:number($raw.stdout;"proof size\\s*:\\s*(?<v>[0-9.]+) KiB"),
 reported_peak_rss_gib:number($raw.stdout;"peak memory (?<v>[0-9.]+) GiB")}
end
