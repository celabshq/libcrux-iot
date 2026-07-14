use libcrux_iot_sha3::{sha224, sha256, sha384, sha512, Sha3_224, Sha3_256, Sha3_384, Sha3_512};
use libcrux_secrets::{Declassify, U8};

fn input_lens(rate: usize) -> Vec<usize> {
    vec![
        0,
        rate / 2,
        rate - 1,
        rate,
        rate + 1,
        2 * rate,
        2 * rate + rate / 2,
        3 * rate,
    ]
}

fn partitionings(rate: usize) -> Vec<Vec<usize>> {
    vec![
        vec![],
        vec![0, rate],
        vec![rate],
        vec![0, rate / 3, rate],
        vec![rate / 2, rate + rate / 2],
        vec![rate / 2, rate / 2, rate, 2 * rate],
        vec![rate - 1, rate],
        vec![rate + 1],
        vec![rate + 1, rate + rate / 2],
        vec![2 * rate - 1, 2 * rate],
        vec![rate, 2 * rate],
        vec![3 * rate],
    ]
}

/// Create a test that tests an incremental sha3 hasher with different input lengths
/// and different partitions of that input against a non-incremental version.
macro_rules! sha3_incremental_hash_test {
    ($test_name:ident, $non_incremental_fn:ident, $incremental_hasher:ty, $rate:literal) => {
        #[test]
        fn $test_name() {
            let input_lens = input_lens($rate);
            let partitionings = partitionings($rate);

            for len in input_lens {
                let input = vec![U8(0); len];
                for partition_points in &partitionings {
                    let mut hasher = <$incremental_hasher>::new();
                    for chunk in partitions(&input, partition_points) {
                        hasher.update(chunk);
                    }
                    let digest = hasher.finish();
                    let expected = $non_incremental_fn(&input);
                    assert_eq!(
                        expected.declassify(),
                        digest.declassify(),
                        "input len: {len} failed with partitioning: {partition_points:?}"
                    );
                }
            }
        }
    };
}

sha3_incremental_hash_test!(sha3_224_incremental_test, sha224, Sha3_224, 144);
sha3_incremental_hash_test!(sha3_256_incremental_test, sha256, Sha3_256, 136);
sha3_incremental_hash_test!(sha3_384_incremental_test, sha384, Sha3_384, 104);
sha3_incremental_hash_test!(sha3_512_incremental_test, sha512, Sha3_512, 72);

/// Partition data into chunks according to the partition_points.
///
/// For `partition_points = &[0, 3, 5]` this will return an iterator over the chunks
/// `[&data[0..0], &data[0..3], &data[3..5], &[5..]]`.  
/// If data is smaller than some partition point, the last chunk will be smaller than
/// requested by the partition point. If the last partition point is smaller than the length
/// of data, the last chunk will be the rest.
fn partitions<'p, 'd: 'p>(
    data: &'d [U8],
    partition_points: &'p [usize],
) -> impl Iterator<Item = &'d [U8]> + 'p {
    let mut partition_points = partition_points.iter();
    let mut offset = 0;
    core::iter::from_fn(move || {
        if let Some(&index) = partition_points.next() {
            debug_assert!(index >= offset, "partition points must be increasing");
            let chunk = data.get(offset..index).or_else(|| data.get(offset..));
            offset = index;
            chunk
        } else {
            let chunk = data.get(offset..);
            // Next iteration, return None by setting offset past the end of data
            offset = data.len() + 1;
            chunk
        }
    })
}
