def positive_integer: type=="number" and .>0 and floor==.;
def validate_pass($count):
  (.iterations|positive_integer) and (.work_items_per_iteration|positive_integer) and
  (.elapsed_ns|length)==$count and all(.elapsed_ns[];positive_integer);
. as $data |
if (([1,2]|index($data.schema_version))==null) or .sampling.outliers_removed!=0 or
   (.measurements|length)==0 or (.sampling.samples_per_case|positive_integer|not) or
   (.sampling.passes|positive_integer|not) or
   ([.measurements[]|[.configuration,.operation]]|length!=(unique|length))
then error("Unsupported or incomplete published measurements") else . end |
.measurements[] | .configuration as $configuration |
if ($data.configurations|has($configuration)|not) then error("Unknown configuration") else . end |
.configuration as $configuration | .operation as $operation |
(if $data.schema_version==1 then [. + {pass:1}] else .passes end) as $passes |
if ($passes|length)!=$data.sampling.passes or
   ([$passes[].pass]|sort)!=[range(1;$data.sampling.passes+1)] or
   any($passes[];validate_pass($data.sampling.samples_per_case)|not)
then error("Missing pass, sample or positive timing denominator") else . end |
$passes[] | .pass as $pass | (.iterations*.work_items_per_iteration) as $denominator |
.elapsed_ns[] | [$configuration,$operation,$pass,(./$denominator)] | @tsv
