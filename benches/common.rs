#[allow(unused_macros)]
macro_rules! gen_benches {
    ($bench:ident, $(($target:ident, $event:path)),+) => {
        #[cfg(all(feature = "bench-perf-events", target_arch = "x86_64"))]
        paste::paste! {
            $(
                fn $target(c: &mut Criterion<criterion_perf_events::Perf>) {
                    $bench(c, stringify!($target));
                }


                criterion::criterion_group! {
                    name = [<group_ $target>];
                    config = Criterion::default()
                    .with_measurement(
                        criterion_perf_events::Perf::new(
                            perfcnt::linux::PerfCounterBuilderLinux::from_hardware_event($event),
                        )
                    );
                    targets = $target
                }
            )+

            criterion::criterion_main!($([<group_ $target>]),+);
        }

        #[cfg(not(all(feature = "bench-perf-events", target_arch = "x86_64")))]
        fn default_run(c: &mut Criterion<criterion::measurement::WallTime>) {
            $bench(c, "default");
        }

        #[cfg(not(all(feature = "bench-perf-events", target_arch = "x86_64")))]
        criterion::criterion_group!(
            name = default_bench;
            config = Criterion::default();
            targets = default_run
        );

        #[cfg(not(all(feature = "bench-perf-events", target_arch = "x86_64")))]
        criterion::criterion_main!(default_bench);
    };
}
