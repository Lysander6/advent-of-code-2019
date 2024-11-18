use std::str::FromStr;

use anyhow::{anyhow, bail, Context};

#[derive(Debug, Eq, PartialEq)]
pub struct Problem {
    program: Vec<u64>,
}

impl FromStr for Problem {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.trim()
            .split(',')
            .map(str::parse)
            .collect::<Result<Vec<_>, _>>()
            .map(|program| Problem { program })
    }
}

const ADD: u64 = 1;
const MULTIPLY: u64 = 2;
const HALT: u64 = 99;

fn run_program(mut program: Vec<u64>) -> Result<Vec<u64>, anyhow::Error> {
    let mut i = 0;

    while let Some(&opcode) = program.get(i) {
        match opcode {
            ADD | MULTIPLY => {
                let [a_pos, b_pos, dest_pos] = match program.get(i + 1..=i + 3) {
                    Some(params) => params
                        .try_into()
                        .with_context(|| format!("Couldn't cast {:?} into [usize; 3]", params))?,
                    None => bail!("Missing parameters for opcode {} at position {}", opcode, i),
                };

                let a = *program
                    .get(a_pos as usize)
                    .ok_or_else(|| anyhow!("Invalid position a_pos {}", a_pos))?;
                let b = *program
                    .get(b_pos as usize)
                    .ok_or_else(|| anyhow!("Invalid position b_pos {}", b_pos))?;
                let dest = program
                    .get_mut(dest_pos as usize)
                    .ok_or_else(|| anyhow!("Invalid position dest_pos {}", dest_pos))?;

                *dest = if opcode == ADD { a + b } else { a * b };

                i += 4;
            }
            HALT => {
                break;
            }
            _ => bail!("Unexpected opcode: {}", opcode),
        }
    }

    Ok(program)
}

fn set_noun_and_verb(program: &mut Vec<u64>, noun: u64, verb: u64) -> Result<(), anyhow::Error> {
    if let Some(n) = program.get_mut(1) {
        *n = noun;
    } else {
        bail!("Program too short to set noun");
    };

    if let Some(v) = program.get_mut(2) {
        *v = verb;
    } else {
        bail!("Program too short to set verb");
    };

    Ok(())
}

pub fn solve_part_1(p: &Problem) -> Result<u64, anyhow::Error> {
    let mut program = p.program.clone();

    set_noun_and_verb(&mut program, 12, 2)?;

    run_program(program).map(|result| result[0])
}

pub fn solve_part_2(p: &Problem) -> Result<u64, anyhow::Error> {
    for noun in 0..=99 {
        for verb in 0..=99 {
            let mut program = p.program.clone();

            set_noun_and_verb(&mut program, noun, verb)?;

            let result = run_program(program).map(|result| result[0])?;

            if result == 19690720 {
                return Ok(100 * noun + verb);
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
        assert_eq!(
            run_program(vec![1, 0, 0, 0, 99]).unwrap(),
            vec![2, 0, 0, 0, 99]
        )
    }

    #[test]
    fn test_run_program_2() {
        assert_eq!(
            run_program(vec![2, 3, 0, 3, 99]).unwrap(),
            vec![2, 3, 0, 6, 99]
        )
    }

    #[test]
    fn test_run_program_3() {
        assert_eq!(
            run_program(vec![2, 4, 4, 5, 99, 0]).unwrap(),
            vec![2, 4, 4, 5, 99, 9801]
        )
    }

    #[test]
    fn test_run_program_4() {
        assert_eq!(
            run_program(vec![1, 1, 1, 4, 99, 5, 6, 0, 99]).unwrap(),
            vec![30, 1, 1, 4, 2, 5, 6, 0, 99]
        )
    }

    #[test]
    fn test_run_program_5() {
        assert_eq!(
            run_program(vec![1, 9, 10, 3, 2, 3, 11, 0, 99, 30, 40, 50]).unwrap(),
            vec![3500, 9, 10, 70, 2, 3, 11, 0, 99, 30, 40, 50]
        )
    }
}
