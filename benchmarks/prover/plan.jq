def csv($v;$default): if $v=="" then $default else $v|split(",") end;
def known($wanted;$allowed;$label): if ($wanted|length)==0 or ($wanted|length)!=($wanted|unique|length) or ($wanted-$allowed|length)>0 then error("Unknown or empty "+$label) else $wanted end;
. as $c | ($c.presets[$preset]//error("Unknown preset")) as $preset |
known(csv($revisions;($c.revisions|keys));($c.revisions|keys);"revision") as $revisions |
known(csv($provers;$c.provers);$c.provers;"prover") as $provers |
known(csv($workloads;$preset.workloads);($c.workloads|keys);"workload") as $workloads |
($c.targets[$target]//error("Unknown target")) as $flags |
(if $threads=="" then ($preset.threads|map([.,($cpus|length)]|min)|unique) else csv($threads;[])|map(tonumber) end) as $threads |
(if $repeat=="" then $preset.repeat else $repeat|tonumber end) as $repeat |
(if $rate=="" then $c.log_inverse_rate else $rate|tonumber end) as $rate |
if $repeat<2 or $repeat>128 or ($repeat|floor)!=$repeat or ($threads|length)==0 or
 any($threads[];. < 1 or .>($cpus|length) or floor!=.) or ($rate|floor)!=$rate or $rate<1 or $rate>4
then error("Invalid repeat, worker count or inverse rate") else . end |
(if $target=="native" then [] elif $target=="avx2" then ["avx2"]
 elif $target=="avx2-gfni" then ["avx2","gfni","pclmulqdq","vpclmulqdq"]
 else ["avx512f","avx512bw","avx512cd","avx512dq","avx512vl"] end) as $required |
[$required[]|select($capabilities.features[.]!=true)] as $missing |
if ($missing|length)>0 then error("Unsupported CPU/OS features: "+($missing|join(","))) else
{schema_version:2,target:$target,rustflags:$flags,capabilities:$capabilities,repeat:$repeat,cooldown_seconds:$c.cooldown_seconds,
 log_inverse_rate:$rate,shuffle_seed:$c.shuffle_seed,fixture_preparation:"Separate processes; matching cache hashes before timing",
 jobs:[$revisions[] as $r | $provers[] as $p | $threads[] as $n | $workloads[] as $w |
  {revision:$r,sha:$c.revisions[$r],prover:$p,threads:$n,cpus:$cpus[:$n],workload:$w,arguments:$c.workloads[$w]}]}
end
