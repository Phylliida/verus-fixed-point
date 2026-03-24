#[cfg(verus_keep_ghost)]
pub mod fixed_point;
#[cfg(verus_keep_ghost)]
pub use fixed_point::FixedPoint;

pub mod runtime_fixed_point;
pub use runtime_fixed_point::RuntimeFixedPoint;
