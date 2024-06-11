#[cfg(feature = "gen-benches-macro")]
#[macro_export]
macro_rules! gen_benches {
    ($bench:ident, $(($target:ident, $event:path)),+) => {
        use paste::paste;
        use criterion::{criterion_group, criterion_main};

        #[cfg(feature = "perf-events")]
        paste! {
            $(
                fn $target(c: &mut Criterion<criterion_perf_events::Perf>) {
                    $bench(c, stringify!($target));
                }


                criterion_group! {
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

            criterion_main!($([<group_ $target>]),+);
        }

        #[cfg(not(feature = "perf-events"))]
        fn default_run(c: &mut Criterion<criterion::measurement::WallTime>) {
            $bench(c, "default");
        }

        #[cfg(not(feature = "perf-events"))]
        criterion_group!(
            name = default_bench;
            config = Criterion::default();
            targets = default_run
        );

        #[cfg(not(feature = "perf-events"))]
        criterion_main!(default_bench);
    };
}
