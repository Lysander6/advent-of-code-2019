use std::str::FromStr;

#[derive(Debug, Eq, PartialEq)]
pub struct Problem {
    program: Vec<u64>,
}

impl FromStr for Problem {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let program = s
            .trim()
            .split(',')
            .map(str::parse)
            .collect::<Result<_, _>>()?;

        Ok(Problem { program })
    }
}

const ADD: u64 = 1;
const MULTIPLY: u64 = 2;
const HALT: u64 = 99;

fn run_program(mut program: Vec<u64>) -> Vec<u64> {
    let mut i = 0;

    while let Some(&v) = program.get(i) {
        match v {
            ADD | MULTIPLY => {
                let a_pos = program[i + 1] as usize;
                let b_pos = program[i + 2] as usize;
                let dest = program[i + 3] as usize;
                let a = program[a_pos];
                let b = program[b_pos];

                program[dest] = if v == ADD { a + b } else { a * b };

                i += 4;
            }
            HALT => {
                break;
            }
            _ => unreachable!(),
        }
    }

    program
}

pub fn solve_part_1(p: &Problem) -> u64 {
    let mut program = p.program.clone();
    program[1] = 12;
    program[2] = 2;

    run_program(program)[0]
}

pub fn solve_part_2(p: &Problem) -> u64 {
    for noun in 0..=99 {
        for verb in 0..=99 {
            let mut program = p.program.clone();
            program[1] = noun;
            program[2] = verb;

            let result = run_program(program)[0];

            if result == 19690720 {
                return 100 * noun + verb;
            }
        }
    }

    unreachable!()
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_INPUT: &str = "1,9,10,3,2,3,11,0,99,30,40,50";

    #[test]
    fn test_problem_parsing() {
        let p: Problem = TEST_INPUT.parse().unwrap();

        assert_eq!(
            p,
            Problem {
                program: vec![1, 9, 10, 3, 2, 3, 11, 0, 99, 30, 40, 50]
            }
        )
    }

    #[test]
    fn test_run_program_1() {
        assert_eq!(run_program(vec![1, 0, 0, 0, 99]), vec![2, 0, 0, 0, 99])
    }

    #[test]
    fn test_run_program_2() {
        assert_eq!(run_program(vec![2, 3, 0, 3, 99]), vec![2, 3, 0, 6, 99])
    }

    #[test]
    fn test_run_program_3() {
        assert_eq!(
            run_program(vec![2, 4, 4, 5, 99, 0]),
            vec![2, 4, 4, 5, 99, 9801]
        )
    }

    #[test]
    fn test_run_program_4() {
        assert_eq!(
            run_program(vec![1, 1, 1, 4, 99, 5, 6, 0, 99]),
            vec![30, 1, 1, 4, 2, 5, 6, 0, 99]
        )
    }

    #[test]
    fn test_run_program_5() {
        assert_eq!(
            run_program(vec![1, 9, 10, 3, 2, 3, 11, 0, 99, 30, 40, 50]),
            vec![3500, 9, 10, 70, 2, 3, 11, 0, 99, 30, 40, 50]
        )
    }
}
