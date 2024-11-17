use core::str::FromStr;

#[derive(Debug, Eq, PartialEq)]
pub struct Problem {
    pub module_masses: Vec<u64>,
}

impl FromStr for Problem {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let module_masses = s.lines().map(str::parse).collect::<Result<Vec<_>, _>>()?;

        Ok(Problem { module_masses })
    }
}

fn required_fuel(mass: u64) -> Option<u64> {
    (mass / 3).checked_sub(2)
}

pub fn solve_part_1(p: &Problem) -> u64 {
    p.module_masses
        .iter()
        .filter_map(|&mass| required_fuel(mass))
        .sum()
}

fn required_fuel_with_more_fuel(mass: u64) -> u64 {
    std::iter::successors(required_fuel(mass), |&fuel| required_fuel(fuel)).sum()
}

pub fn solve_part_2(p: &Problem) -> u64 {
    p.module_masses
        .iter()
        .map(|&mass| required_fuel_with_more_fuel(mass))
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_INPUT: &str = "\
12
14
1969
100756";

    #[test]
    fn test_problem_parsing() {
        let result: Problem = TEST_INPUT.parse().unwrap();

        assert_eq!(
            result,
            Problem {
                module_masses: vec![12, 14, 1969, 100756]
            }
        );
    }

    #[test]
    fn test_required_fuel() {
        assert_eq!(required_fuel(12), Some(2));
        assert_eq!(required_fuel(14), Some(2));
        assert_eq!(required_fuel(1969), Some(654));
        assert_eq!(required_fuel(100756), Some(33583));
    }

    #[test]
    fn test_solve_part_1() {
        let problem = TEST_INPUT.parse().unwrap();

        assert_eq!(solve_part_1(&problem), 34241);
    }

    #[test]
    fn test_required_fuel_with_more_fuel() {
        assert_eq!(required_fuel_with_more_fuel(12), 2);
        assert_eq!(required_fuel_with_more_fuel(14), 2);
        assert_eq!(required_fuel_with_more_fuel(1969), 966);
        assert_eq!(required_fuel_with_more_fuel(100756), 50346);
    }

    #[test]
    fn test_solve_part_2() {
        let problem = TEST_INPUT.parse().unwrap();

        assert_eq!(solve_part_2(&problem), 2 + 2 + 966 + 50346);
    }
}
