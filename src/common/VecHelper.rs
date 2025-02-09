/// v1 \ v2 = return
pub fn setminus<T: PartialEq + Clone>(v1: &Vec<T>, v2: &Vec<T>) -> Vec<T> {
    let mut result = v1.clone();

    for elem in v2 {
        let idx = result.iter().position(|x| *x == *elem);

        if idx.is_none() {
            continue;
        }

        result.swap_remove(idx.unwrap());
    }

    result
}

/// v1 \cap v2 = result
pub fn intersect<T: Eq + Clone>(v1: &Vec<T>, v2: &Vec<T>) -> Vec<T> {
    let mut result = Vec::new();

    for elem in v2 {
        if v1.contains(elem) {
            result.push(elem.clone());
        }
    }

    result
}