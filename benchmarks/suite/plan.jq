def csv($text;$fallback): if $text=="" then $fallback else $text|split(",") end;
def only_known($wanted;$known;$label):
  if ($wanted|length)==0 or ($wanted|length)!=($wanted|unique|length) or ($wanted- $known|length)>0 then error("Unknown or empty "+$label+": "+($wanted|join(","))) else $wanted end;
def int_or($value;$fallback): if $value=="" then $fallback else $value|tonumber end;
. as $config |
($config.profiles[$profile] // error("Unknown profile: "+$profile)) as $defaults |
($defaults+{samples:int_or($samples;$defaults.samples),sample_ms:int_or($sample_ms;$defaults.sample_ms),
  passes:int_or($passes;$defaults.passes),groups:csv($groups;$defaults.groups),
  per_fixture:($per_fixture or $defaults.per_fixture)}) as $settings |
only_known(csv($targets;[$config.targets[].id]);[$config.targets[].id];"CPU targets") as $targets |
only_known(csv($hashing;$config.keccak);$config.keccak;"hash backends") as $hashes |
only_known(csv($recovery;$config.ecrecover);$config.ecrecover;"recovery providers") as $recoveries |
only_known($settings.groups;["direct","macro","batched","reject","hash","ecrecover"];"case groups") as $groups |
if $settings.samples<5 or $settings.samples>100000 or $settings.sample_ms<10 or $settings.sample_ms>60000 or
   $settings.passes<1 or $settings.passes>100 then error("Invalid sample/pass bounds") else . end |
if any($groups[];.=="direct" or .=="batched") and ($settings.samples%(3+$settings.extra_cases)!=0)
then error("Samples must be a multiple of the shared signature corpus size") else . end |
[$config.targets[] | select(.id as $id|$targets|index($id)) |
  (if .id=="native" and $capabilities.architecture!="x86_64" then .requires=[] else . end) |
  . as $target |
  ([.requires[]|select($capabilities.features[.]!=true)] +
   (if .id!="native" and $capabilities.architecture!="x86_64" then ["x86_64"] else [] end)) as $missing |
  if ($missing|length)>0 then {skipped:{target:.id,missing:$missing,reason:"Unsupported CPU/OS features"}}
  else $hashes[] as $hash | $recoveries[] as $provider |
    select($provider!="k256" or any($groups[];.=="macro" or .=="ecrecover")) |
    (if $provider=="k256" then ["ecrecover"] else $groups end) as $cases |
    ($disable_slp or ($hash=="tiny" and (["v3","v4","native"]|index($target.id))!=null and
      $capabilities.features.avx2==true and ($unmodified_tiny|not))) as $no_slp |
    {job:{id:($target.id+"-"+$hash+"-"+$provider+(if $no_slp then "-no-slp" else "" end)),target:$target,
      keccak:$hash,ecrecover:$provider,groups:$cases,
      features:([if $provider=="libsecp256k1" then "secp256k1" else empty end,
                 if $hash=="assembly" then "asm-keccak" else empty end,
                 if $hash=="tiny" then "tiny-keccak" else empty end,
                 if $cases|index("batched") then "experimental-simd" else empty end]),
      extra_rustflags:(if $no_slp then ["-C","no-vectorize-slp"] else [] end),
      case_count:((if $cases|index("macro") then (if $settings.per_fixture then 29 else 8 end) else 0 end)+
        (if $cases|index("direct") then 6 else 0 end)+(if $cases|index("batched") then 3 else 0 end)+
        (if $cases|index("reject") then 16 else 0 end)+(if $cases|index("hash") then 42 else 0 end)+
        (if ($cases|index("ecrecover")) and ($cases|index("macro")|not) then 1 else 0 end))}}
  end] as $choices |
[$choices[]|.job//empty] as $jobs |
if ($jobs|length)==0 then error("No supported configurations") else
{schema_version:2,profile_name:$profile,profile:$settings,toolchain:$config.toolchain,cpu:$cpu,seed:$config.seed,
 cooldown_seconds:int_or($cooldown;($defaults.cooldown_seconds//$config.cooldown_seconds)),capabilities:$capabilities,
 jobs:$jobs,skipped:[$choices[]|.skipped//empty],
 minimum_sampling_hours:(([$jobs[].case_count]|add)*$settings.samples*$settings.sample_ms*$settings.passes/3600000),
 duration_note:"Lower bound excludes calibration, fixtures, long single operations and cooldown"} end
