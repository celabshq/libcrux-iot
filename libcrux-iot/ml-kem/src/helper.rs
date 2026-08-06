/// The following macros are defined so that the extraction from Rust to C code
/// can go through.

#[cfg(eurydice)]
macro_rules! cloop {
    (for ($i:ident, $chunk:ident) in $val:ident.$values:ident.chunks_exact($($chunk_size:expr),*).enumerate() $body:block) => {
        for $i in 0..$val.$values.len() / ($($chunk_size)*) {
            let $chunk = &$val.$values[$i*($($chunk_size)*) .. $i*($($chunk_size)*)+($($chunk_size)*)];
            $body
        }
    };
    (for ($i:ident, $chunk:ident) in $val:ident.chunks_exact($($chunk_size:expr),*).enumerate() $body:block) => {
        for $i in 0..$val.len() / ($($chunk_size)*) {
            let $chunk = &$val[$i*($($chunk_size)*) .. $i*($($chunk_size)*)+($($chunk_size)*)];
            $body
        }
    };
    (for ($i:ident, $item:ident) in $val:ident.iter().enumerate() $body:block) => {
        for $i in 0..$val.len() {
            let $item = &$val[$i];
            $body
        }
    };
    (for ($i:ident, $item:ident) in $val:ident.into_iter().enumerate() $body:block) => {
        for $i in 0..$val.len() {
            let $item = $val[$i];
            $body
        }
    };
    (for $i:ident in ($start:literal..$end:expr).step_by($step:literal) $body:block) => {{
        let mut $i = $start;
        let step = $step;
        let end = $end;
        // This is only needed for type inference to connect the types of $i and $end.
        // Otherwise we can't call checked_add for some usages of cloop.
        // Optimized out by eurydice.
        if false {
            let _ = $i >= end;
        }
        // If $body contains a `continue`, we would enter an infinite loop if we did the
        // step_by addition after the $body. Instead, we initialize $i with $start and
        // do the step_by increase before the $body, except on the first iteration.
        let mut first_iter = true;
        loop {
            if !first_iter {
                // This guards against the $i overflowing its type,
                // in that case break from the loop
                $i = match $i.checked_add(step) {
                    Some(v) => v,
                    None => break
                };
            }
            first_iter = false;
            if $i >= end {
                break;
            }
            $body
        }
    }};
}

#[cfg(not(eurydice))]
macro_rules! cloop {
    (for ($i:ident, $chunk:ident) in $val:ident.$values:ident.chunks_exact($($chunk_size:expr),*).enumerate() $body:block) => {
        for ($i, $chunk) in $val.$values.chunks_exact($($chunk_size),*).enumerate() $body
    };
    (for ($i:ident, $chunk:ident) in $val:ident.chunks_exact($($chunk_size:expr),*).enumerate() $body:block) => {
        for ($i, $chunk) in $val.chunks_exact($($chunk_size),*).enumerate() $body
    };
    (for ($i:ident, $item:ident) in $val:ident.iter().enumerate() $body:block) => {
        for ($i, $item) in $val.iter().enumerate() $body
    };
    (for ($i:ident, $item:ident) in $val:ident.into_iter().enumerate() $body:block) => {
        for ($i, $item) in $val.into_iter().enumerate() $body
    };
    (for $i:ident in ($start:literal..$end:expr).step_by($step:literal) $body:block) => {
        for $i in ($start..$end).step_by($step) $body
    };
}

pub(crate) use cloop;
