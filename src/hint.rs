use core::hint::cold_path;

/// Hints to the compiler that a branch condition is unlikely to be true.
/// Returns the value passed to it.
///
/// It can be used with `if` or boolean `match` expressions.
///
/// When used outside of a branch condition, it may still influence a nearby
/// branch, but probably will not have any effect.
#[inline(always)]
pub const fn likely(b: bool) -> bool {
    if !b {
        cold_path();
    }
    b
}

/// Hints to the compiler that given path is cold, i.e., unlikely to be taken.
/// The compiler may choose to optimize paths that are not cold at the expense
/// of paths that are cold.
///
/// Any use other than with `if` statements will probably not have an effect.
///
/// Note that, unlike most intrinsics, this is safe to call;
/// it does not require an `unsafe` block. Therefore, implementations must not
/// require the user to uphold any safety invariants.
#[inline(always)]
pub const fn unlikely(b: bool) -> bool {
    if b {
        cold_path();
    }
    b
}
