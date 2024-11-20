use std::{env, fs};

use anyhow::{anyhow, Context};
use day_03::{solve_part_1, solve_part_2, Problem};

fn main() -> Result<(), anyhow::Error> {
    let input_path = env::args().nth(1).context("missing path argument")?;
    let input = fs::read_to_string(input_path)?;
    let p: Problem = input.parse()?;

    println!("Part 1: {}", solve_part_1(&p).2);
    println!(
        "Part 2: {}",
        solve_part_2(&p).ok_or_else(|| anyhow!("No solution found"))?
    );

    Ok(())
}
