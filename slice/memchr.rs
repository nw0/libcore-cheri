/// Return the first index matching the byte `x` in `text`.
pub fn memchr(x: u8, text: &[u8]) -> Option<usize> {
    // The simplest implementation possible, but return halfway
    // Attempting to avoid optimisation, which becomes pointer manipulation
    // that CHERI cannot handle.
    // In particular, this doesn't work: text.iter().position(|elt| *elt == x)

    let mut i = 0;
    for c in text {
        if *c == x {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Return the last index matching the byte `x` in `text`.
pub fn memrchr(x: u8, text: &[u8]) -> Option<usize> {
    // Ditto from memchr

    let mut i = text.len() - 1;
    // Pre: i >= 0
    loop {
        if text[i] == x {
            return Some(i)
        }
        // Mid: i >= 0; i-- cont if i > 0, oth term
        if i == 0 {
            return None
        }
        i -= 1;
    }
}
