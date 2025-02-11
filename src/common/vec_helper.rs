/// Computes set difference (v1 \ v2) and returns a new copy as the result.
pub fn setminus<T: PartialEq + Clone>(v1: &[T], v2: &[T]) -> Vec<T> {
    let mut result = v1.to_vec();

    for elem in v2 {
        let idx = result.iter().position(|x| *x == *elem);

        if idx.is_none() {
            continue;
        }

        result.swap_remove(idx.unwrap());
    }

    result
}
