use std::{
    collections::{hash_map, HashMap},
    str::FromStr,
};

use anyhow::anyhow;

#[derive(Debug, Eq, PartialEq)]
pub struct Problem {
    first_wire_horizontal_segments: HashMap<i32, (i32, i32)>, // y -> (x_min, x_max)
    first_wire_vertical_segments: HashMap<i32, (i32, i32)>,   // x -> (y_min, y_max)
    second_wire_horizontal_segments: HashMap<i32, (i32, i32)>, // y -> (x_min, x_max)
    second_wire_vertical_segments: HashMap<i32, (i32, i32)>,  // x -> (y_min, y_max)
}

//
// y ^
//   |
//   |
// 0 +-----> x
//   0

impl FromStr for Problem {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut first_wire_horizontal_segments = HashMap::new();
        let mut first_wire_vertical_segments = HashMap::new();
        let mut second_wire_horizontal_segments = HashMap::new();
        let mut second_wire_vertical_segments = HashMap::new();

        let (first_wire_path, second_wire_path) = s
            .trim()
            .split_once('\n')
            .ok_or_else(|| anyhow!("Couldn't split on newline"))?;

        wire_path_to_segments(
            first_wire_path,
            &mut first_wire_horizontal_segments,
            &mut first_wire_vertical_segments,
        )?;
        wire_path_to_segments(
            second_wire_path,
            &mut second_wire_horizontal_segments,
            &mut second_wire_vertical_segments,
        )?;

        Ok(Problem {
            first_wire_horizontal_segments,
            first_wire_vertical_segments,
            second_wire_horizontal_segments,
            second_wire_vertical_segments,
        })
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Interval {
    low: i32,
    high: i32,
    key: i32,
}

#[derive(Debug)]
struct Node {
    interval: Interval,
    max: i32,
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

impl Node {
    fn new(interval: Interval) -> Self {
        let max = interval.high;

        Self {
            interval,
            max,
            left: None,
            right: None,
        }
    }

    fn insert(&mut self, new_interval: Interval) {
        self.max = self.max.max(new_interval.high);

        if new_interval.low < self.interval.low {
            if let Some(ref mut left_child) = self.left {
                left_child.insert(new_interval);
            } else {
                self.left = Some(Box::new(Node::new(new_interval)));
            }
        } else if let Some(ref mut right_child) = self.right {
            right_child.insert(new_interval);
        } else {
            self.right = Some(Box::new(Node::new(new_interval)));
        }
    }

    fn search<'a>(&'a self, point: i32, result: &mut Vec<&'a Interval>) {
        if self.interval.low <= point && point <= self.interval.high {
            result.push(&self.interval);
        }

        if let Some(ref left_child) = self.left {
            if left_child.max >= point {
                left_child.search(point, result);
            }
        }

        if let Some(ref right_child) = self.right {
            right_child.search(point, result);
        }
    }
}

#[derive(Debug)]
struct IntervalTree {
    root: Option<Node>,
}

impl IntervalTree {
    fn new() -> Self {
        Self { root: None }
    }

    fn insert(&mut self, interval: Interval) {
        match self.root {
            Some(ref mut node) => node.insert(interval),
            None => self.root = Some(Node::new(interval)),
        }
    }

    fn search(&self, point: i32) -> Vec<&Interval> {
        let mut result = Vec::new();

        if let Some(ref node) = self.root {
            node.search(point, &mut result);
        }

        result
    }
}

fn wire_path_to_segments(
    wire_path: &str,
    horizontal_segments: &mut HashMap<i32, (i32, i32)>,
    vertical_segments: &mut HashMap<i32, (i32, i32)>,
) -> Result<(), anyhow::Error> {
    let (mut x, mut y) = (0, 0);

    for instr in wire_path.split(',') {
        let (dir, len) = instr.split_at(1);
        let len: i32 = len.parse()?;

        match dir {
            "U" | "D" => {
                let y_start = y;
                let y_end = if dir == "U" { y + len } else { y - len };
                let entry = if dir == "U" {
                    (y_start, y_end)
                } else {
                    (y_end, y_start)
                };

                match vertical_segments.entry(x) {
                    hash_map::Entry::Occupied(_) => {
                        unreachable!("assumed input property is not met")
                    }
                    hash_map::Entry::Vacant(v) => v.insert(entry),
                };

                y = y_end;
            }
            "R" | "L" => {
                let x_start = x;
                let x_end = if dir == "R" { x + len } else { x - len };
                let entry = if dir == "R" {
                    (x_start, x_end)
                } else {
                    (x_end, x_start)
                };

                match horizontal_segments.entry(y) {
                    hash_map::Entry::Occupied(_) => {
                        unreachable!("assumed input property is not met")
                    }
                    hash_map::Entry::Vacant(v) => v.insert(entry),
                };

                x = x_end;
            }
            _ => unreachable!("Unknown dir {}", dir),
        }
    }
    Ok(())
}

// order keys by abs value
// can stop once one dimension distance is larger than closest found distance to this point (if any found)

#[must_use]
pub fn solve_part_1(p: &Problem) -> (i32, i32, i32) {
    let Problem {
        first_wire_horizontal_segments,
        first_wire_vertical_segments,
        second_wire_horizontal_segments,
        second_wire_vertical_segments,
    } = p;

    let mut second_wire_horizontal_intervals = IntervalTree::new();
    let mut second_wire_vertical_intervals = IntervalTree::new();

    for (y, (x_min, x_max)) in second_wire_horizontal_segments {
        second_wire_horizontal_intervals.insert(Interval {
            low: *x_min,
            high: *x_max,
            key: *y,
        });
    }

    for (x, (y_min, y_max)) in second_wire_vertical_segments {
        second_wire_vertical_intervals.insert(Interval {
            low: *y_min,
            high: *y_max,
            key: *x,
        });
    }

    let second_wire_horizontal_intervals = second_wire_horizontal_intervals;
    let second_wire_vertical_intervals = second_wire_vertical_intervals;

    let mut min_x = 999_999;
    let mut min_y = 999_999;
    let mut min_dist = 999_999_999;

    for (&y, &(x_min, x_max)) in first_wire_horizontal_segments {
        for &Interval { key: x, .. } in second_wire_vertical_intervals.search(y) {
            if (x_min <= x && x <= x_max) && !(x == 0 && y == 0) && x.abs() + y.abs() < min_dist {
                min_x = x;
                min_y = y;
                min_dist = x.abs() + y.abs();
            }
        }
    }

    for (&x, &(y_min, y_max)) in first_wire_vertical_segments {
        for &Interval { key: y, .. } in second_wire_horizontal_intervals.search(x) {
            if (y_min <= y && y <= y_max) && !(x == 0 && y == 0) && x.abs() + y.abs() < min_dist {
                min_x = x;
                min_y = y;
                min_dist = x.abs() + y.abs();
            }
        }
    }

    (min_x, min_y, min_dist)
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_INPUT: &str = "\
R8,U5,L5,D3
U7,R6,D4,L4
";

    #[test]
    fn test_problem_parsing() {
        let p: Problem = TEST_INPUT.parse().unwrap();

        assert_eq!(
            p,
            Problem {
                first_wire_horizontal_segments: HashMap::from([(0, (0, 8)), (5, (3, 8))]),
                first_wire_vertical_segments: HashMap::from([(8, (0, 5)), (3, (2, 5))]),
                second_wire_horizontal_segments: HashMap::from([(3, (2, 6)), (7, (0, 6))]),
                second_wire_vertical_segments: HashMap::from([(0, (0, 7)), (6, (3, 7))]),
            }
        );
    }

    #[test]
    fn test_solve_part1_1() {
        let p: Problem = TEST_INPUT.parse().unwrap();

        assert_eq!(solve_part_1(&p), (3, 3, 6));
    }

    #[test]
    fn test_solve_part1_2() {
        let p: Problem = "\
R75,D30,R83,U83,L12,D49,R71,U7,L72
U62,R66,U55,R34,D71,R55,D58,R83"
            .parse()
            .unwrap();

        assert_eq!(solve_part_1(&p).2, 159);
    }

    #[test]
    fn test_solve_part1_3() {
        let p: Problem = "\
R98,U47,R26,D63,R33,U87,L62,D20,R33,U53,R51
U98,R91,D20,R16,D67,R40,U7,R15,U6,R7"
            .parse()
            .unwrap();

        assert_eq!(solve_part_1(&p).2, 135);
    }
}
