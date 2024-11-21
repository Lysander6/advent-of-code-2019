#![allow(clippy::many_single_char_names)]

#[must_use]
pub fn dumb(min: u32, max: u32) -> usize {
    let mut current = min;
    let mut count = 0;

    while current <= max {
        let (a, b, c, d, e, f) = (
            current / 100_000 % 10,
            current / 10_000 % 10,
            current / 1_000 % 10,
            current / 100 % 10,
            current / 10 % 10,
            current % 10,
        );

        if a <= b
            && b <= c
            && c <= d
            && d <= e
            && e <= f
            && (a == b || b == c || c == d || d == e || e == f)
        {
            count += 1;
        }

        current += 1;
    }

    count
}

#[must_use]
pub fn dumb_part2(min: u32, max: u32) -> usize {
    let mut current = min;
    let mut count = 0;

    while current <= max {
        let (a, b, c, d, e, f) = (
            current / 100_000 % 10,
            current / 10_000 % 10,
            current / 1_000 % 10,
            current / 100 % 10,
            current / 10 % 10,
            current % 10,
        );

        if a <= b
            && b <= c
            && c <= d
            && d <= e
            && e <= f
            && ((a == b && b != c)
                || (a != b && b == c && c != d)
                || (b != c && c == d && d != e)
                || (c != d && d == e && e != f)
                || (d != e && e == f))
        {
            count += 1;
        }

        current += 1;
    }

    count
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_name() {
        let current = 987_654;

        let (a, b, c, d, e, f) = (
            current / 100_000 % 10,
            current / 10_000 % 10,
            current / 1_000 % 10,
            current / 100 % 10,
            current / 10 % 10,
            current % 10,
        );

        assert_eq!((a, b, c, d, e, f), (9, 8, 7, 6, 5, 4));
    }

    #[test]
    fn test_dumb() {
        assert_eq!(dumb(172_930, 683_082), 1675);
    }

    #[test]
    fn test_dumb_part2() {
        assert_eq!(dumb_part2(172_930, 683_082), 1142);
    }
}
