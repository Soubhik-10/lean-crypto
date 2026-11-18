# Input: configuration<TAB>operation<TAB>pass<TAB>batch-average nanoseconds.
# Circular block bootstrap stays within each pass; no samples are removed.
BEGIN { FS="\t"; srand(seed); if (!block) block=10; if (!resamples) resamples=2000 }
function quicksort(a,left,right, i,j,p,t) {
    i=left; j=right; p=a[int((left+right)/2)]
    while(i<=j) {
        while(a[i]<p)i++; while(a[j]>p)j--
        if(i<=j){t=a[i];a[i]=a[j];a[j]=t;i++;j--}
    }
    if(left<j)quicksort(a,left,j); if(i<right)quicksort(a,i,right)
}
function percentile(a,n,f, at,lo,hi) {
    at=1+(n-1)*f;lo=int(at);hi=(at==lo?lo:lo+1)
    return a[lo]+(a[hi]-a[lo])*(at-lo)
}
function median(a,n) { return percentile(a,n,.5) }
function quote(s) { gsub(/\\/,"\\\\",s);gsub(/"/,"\\\"",s);return "\"" s "\"" }
{
    if(NF!=4 || $3<1 || $4<=0 || $4!=$4){print "Invalid normalized sample" > "/dev/stderr";bad=1;exit 1}
    key=$1 SUBSEP $2
    if(!(key in ids)){ids[key]=++groups;configuration[groups]=$1;operation[groups]=$2}
    g=ids[key];p=$3; n=++sizes[g,p];values[g,p,n]=$4
    if(p>passes[g])passes[g]=p
}
END {
    if(bad)exit 1
    for(g=1;g<=groups;g++) {
        srand(seed)
        delete raw;delete boots;delete medians
        total=0;sum=0
        for(p=1;p<=passes[g];p++) {
            n=sizes[g,p];if(!n){print "Missing measurement pass" > "/dev/stderr";exit 1}
            delete work
            for(i=1;i<=n;i++){v=values[g,p,i];raw[++total]=v;work[i]=v;sum+=v}
            quicksort(work,1,n);medians[p]=median(work,n)
        }
        quicksort(raw,1,total);mean=sum/total;variance=0
        for(i=1;i<=total;i++)variance+=(raw[i]-mean)^2
        stdev=(total>1?sqrt(variance/(total-1)):0)
        for(r=1;r<=resamples;r++) {
            delete draw;drawn=0
            for(p=1;p<=passes[g];p++) {
                n=sizes[g,p];taken=0
                while(taken<n) {
                    start=int(rand()*n)
                    for(b=0;b<block && taken<n;b++){draw[++drawn]=values[g,p,1+((start+b)%n)];taken++}
                }
            }
            quicksort(draw,1,drawn);boots[r]=median(draw,drawn)
        }
        quicksort(boots,1,resamples)
        low=medians[1];high=medians[1]
        for(p=2;p<=passes[g];p++){if(medians[p]<low)low=medians[p];if(medians[p]>high)high=medians[p]}
        printf "{\"configuration\":%s,\"name\":%s,\"samples\":%d,\"passes\":%d,",quote(configuration[g]),quote(operation[g]),total,passes[g]
        printf "\"median_ns\":%.17g,\"mean_ns\":%.17g,\"stdev_ns\":%.17g,",median(raw,total),mean,stdev
        printf "\"p05_ns\":%.17g,\"p95_ns\":%.17g,\"p99_ns\":%.17g,\"min_ns\":%.17g,\"max_ns\":%.17g,",percentile(raw,total,.05),percentile(raw,total,.95),percentile(raw,total,.99),raw[1],raw[total]
        printf "\"median_ci95_ns\":[%.17g,%.17g],\"pass_medians_ns\":[",percentile(boots,resamples,.025),percentile(boots,resamples,.975)
        for(p=1;p<=passes[g];p++)printf "%s%.17g",(p==1?"":","),medians[p]
        printf "],\"bootstrap_resamples\":%d,\"bootstrap_block_samples\":%d,\"outliers_removed\":0,\"pass_median_spread_percent\":%.17g,",resamples,block,(high/low-1)*100
        print "\"unit\":\"batch-average ns per operation; batched hashes normalized per input\"}"
    }
}
