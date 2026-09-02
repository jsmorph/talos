/// Return the sequential binary64 dot product of two equally sized arrays.
///
/// # Safety
///
/// When `len` is nonzero, `left` and `right` must each point to `len`
/// initialized `f64` values whose complete ranges are valid for reads. The
/// pointers must satisfy the alignment and provenance requirements of
/// `core::ptr::read` for every indexed element.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn dot(left: *const f64, right: *const f64, len: usize) -> f64 {
    if len == 0 {
        return 0.0;
    }

    let mut sum = unsafe { *left * *right };
    let mut index = 1;
    while index < len {
        let left_value = unsafe { *left.add(index) };
        let right_value = unsafe { *right.add(index) };
        sum += left_value * right_value;
        index += 1;
    }
    sum
}
