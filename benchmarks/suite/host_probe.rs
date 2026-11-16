fn main() {
    macro_rules! flag {
        ($name:tt) => {
            print!("\"{}\":{},", $name, std::is_x86_feature_detected!($name));
        };
    }
    print!(
        "{{\"architecture\":\"{}\",\"features\":{{",
        std::env::consts::ARCH
    );
    #[cfg(target_arch = "x86_64")]
    {
        // CPUID is present on x86-64. Read the extended leaf only when advertised.
        let extended = unsafe { std::arch::x86_64::__cpuid(0x80000000) }.eax;
        let lahf_sahf = extended >= 0x80000001
            && unsafe { std::arch::x86_64::__cpuid(0x80000001) }.ecx & 1 != 0;
        print!("\"lahf_sahf\":{},", lahf_sahf);
        flag!("sse2");
        flag!("sse3");
        flag!("ssse3");
        flag!("sse4.1");
        flag!("sse4.2");
        flag!("popcnt");
        flag!("cmpxchg16b");
        flag!("avx");
        flag!("avx2");
        flag!("bmi1");
        flag!("bmi2");
        flag!("f16c");
        flag!("fma");
        flag!("lzcnt");
        flag!("movbe");
        flag!("avx512f");
        flag!("avx512bw");
        flag!("avx512cd");
        flag!("avx512dq");
        flag!("avx512vl");
    }
    println!("\"probe_complete\":true}}}}");
}
