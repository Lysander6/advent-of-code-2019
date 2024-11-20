use std::{collections::HashMap, str::FromStr};

use anyhow::{anyhow, bail};

#[derive(Debug, Eq, PartialEq)]
pub enum Direction {
    Up,
    Down,
    Right,
    Left,
}

use Direction::{Down, Left, Right, Up};

impl FromStr for Direction {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "U" => Ok(Self::Up),
            "D" => Ok(Self::Down),
            "R" => Ok(Self::Right),
            "L" => Ok(Self::Left),
            d => bail!("Unknown direction: {}", d),
        }
    }
}

// dir, x/y, (p_start, p_end)
type WireSegment = (Direction, i32, (i32, i32));

#[derive(Debug, Eq, PartialEq)]
pub struct Problem {
    first_wire: Vec<WireSegment>,
    second_wire: Vec<WireSegment>,
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
        let (first_wire_path, second_wire_path) = s
            .trim()
            .split_once('\n')
            .ok_or_else(|| anyhow!("Couldn't split on newline"))?;

        let first_wire = parse_wire(first_wire_path)?;
        let second_wire = parse_wire(second_wire_path)?;

        Ok(Problem {
            first_wire,
            second_wire,
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

impl From<&WireSegment> for Interval {
    fn from(value: &WireSegment) -> Self {
        let (_, a, (b1, b2)) = value;

        Self {
            low: *b1.min(b2),
            high: *b1.max(b2),
            key: *a,
        }
    }
}

fn parse_wire(wire_path: &str) -> Result<Vec<WireSegment>, anyhow::Error> {
    let mut result = vec![];
    let (mut x, mut y) = (0, 0);

    for instr in wire_path.split(',') {
        let (dir, len) = instr.split_at(1);
        let dir: Direction = dir.parse()?;
        let len: i32 = len.parse()?;

        match dir {
            Up | Down => {
                let y_start = y;
                let y_end = if dir == Up { y + len } else { y - len };

                result.push((dir, x, (y_start, y_end)));

                y = y_end;
            }
            Right | Left => {
                let x_start = x;
                let x_end = if dir == Right { x + len } else { x - len };

                result.push((dir, y, (x_start, x_end)));

                x = x_end;
            }
        }
    }

    Ok(result)
}

fn find_intersections<'a>(
    first_wire_segment: &WireSegment,
    second_wire_intervals: &'a IntervalTree,
) -> impl Iterator<Item = &'a Interval> {
    let (_, a, (b1, b2)) = first_wire_segment;
    let b_min = *b1.min(b2);
    let b_max = *b1.max(b2);

    return second_wire_intervals
        .search(*a)
        .into_iter()
        .filter(move |Interval { key: b, .. }| b_min <= *b && *b <= b_max);
}

fn make_interval_trees(wire: &[WireSegment]) -> (IntervalTree, IntervalTree) {
    let mut horizontal_intervals = IntervalTree::new();
    let mut vertical_intervals = IntervalTree::new();

    for segment @ (dir, _, _) in wire {
        match dir {
            Up | Down => vertical_intervals.insert(segment.into()),
            Right | Left => horizontal_intervals.insert(segment.into()),
        }
    }

    (horizontal_intervals, vertical_intervals)
}

// order keys by abs value
// can stop once one dimension distance is larger than closest found distance to this point (if any found)

#[must_use]
pub fn solve_part_1(p: &Problem) -> (i32, i32, i32) {
    let Problem {
        first_wire,
        second_wire,
    } = p;

    let (second_wire_horizontal_intervals, second_wire_vertical_intervals) =
        make_interval_trees(second_wire);

    let mut min_x = i32::MAX;
    let mut min_y = i32::MAX;
    let mut min_dist = i32::MAX;

    for first_wire_segment @ (dir, a, _) in first_wire {
        match dir {
            Up | Down => {
                let x = *a;

                for &Interval { key: y, .. } in
                    find_intersections(first_wire_segment, &second_wire_horizontal_intervals)
                {
                    if !(x == 0 && y == 0) && x.abs() + y.abs() < min_dist {
                        min_x = x;
                        min_y = y;
                        min_dist = x.abs() + y.abs();
                    }
                }
            }
            Right | Left => {
                let y = *a;

                for &Interval { key: x, .. } in
                    find_intersections(first_wire_segment, &second_wire_vertical_intervals)
                {
                    if !(x == 0 && y == 0) && x.abs() + y.abs() < min_dist {
                        min_x = x;
                        min_y = y;
                        min_dist = x.abs() + y.abs();
                    }
                }
            }
        }
    }

    (min_x, min_y, min_dist)
}

#[must_use]
pub fn solve_part_2(p: &Problem) -> Option<i32> {
    let Problem {
        first_wire,
        second_wire,
    } = p;

    let mut intersection_points: HashMap<(i32, i32), (i32, i32)> = HashMap::new();

    let (second_wire_horizontal_intervals, second_wire_vertical_intervals) =
        make_interval_trees(second_wire);
    let mut first_wire_distance = 0;

    for first_wire_segment @ (dir, a, (b1, b2)) in first_wire {
        match dir {
            Up | Down => {
                let x = *a;
                let intersections =
                    find_intersections(first_wire_segment, &second_wire_horizontal_intervals);

                for &Interval { key: y, .. } in intersections {
                    if !(x == 0 && y == 0) {
                        // TODO: maybe consider note form the puzzle "If a wire visits a position on the grid multiple times (...)"
                        intersection_points.entry((x, y)).or_default().0 =
                            first_wire_distance + (b1 - y).abs();
                    }
                }
            }
            Right | Left => {
                let y = *a;
                let intersections =
                    find_intersections(first_wire_segment, &second_wire_vertical_intervals);

                for &Interval { key: x, .. } in intersections {
                    if !(x == 0 && y == 0) {
                        intersection_points.entry((x, y)).or_default().0 =
                            first_wire_distance + (b1 - x).abs();
                    }
                }
            }
        }

        first_wire_distance += (b1 - b2).abs();
    }

    let (first_wire_horizontal_intervals, first_wire_vertical_intervals) =
        make_interval_trees(first_wire);
    let mut second_wire_distance = 0;

    for second_wire_segment @ (dir, a, (b1, b2)) in second_wire {
        match dir {
            Up | Down => {
                let x = *a;
                let intersections =
                    find_intersections(second_wire_segment, &first_wire_horizontal_intervals);

                for &Interval { key: y, .. } in intersections {
                    if !(x == 0 && y == 0) {
                        intersection_points.entry((x, y)).or_default().1 = // by this point record with key `(x, y)` exists
                            second_wire_distance + (b1 - y).abs();
                    }
                }
            }
            Right | Left => {
                let y = *a;
                let intersections =
                    find_intersections(second_wire_segment, &first_wire_vertical_intervals);

                for &Interval { key: x, .. } in intersections {
                    if !(x == 0 && y == 0) {
                        intersection_points.entry((x, y)).or_default().1 =
                            second_wire_distance + (b1 - x).abs();
                    }
                }
            }
        }

        second_wire_distance += (b1 - b2).abs();
    }

    intersection_points
        .values()
        .min_by(|a, b| (a.0 + a.1).cmp(&(b.0 + b.1)))
        .map(|a| a.0 + a.1)
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
                first_wire: vec![
                    (Right, 0, (0, 8)),
                    (Up, 8, (0, 5)),
                    (Left, 5, (8, 3)),
                    (Down, 3, (5, 2))
                ],
                second_wire: vec![
                    (Up, 0, (0, 7)),
                    (Right, 7, (0, 6)),
                    (Down, 6, (7, 3)),
                    (Left, 3, (6, 2))
                ],
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

    #[test]
    fn test_solve_part2_1() {
        let p: Problem = TEST_INPUT.parse().unwrap();

        assert_eq!(solve_part_2(&p), Some(30));
    }

    #[test]
    fn test_solve_part2_2() {
        let p: Problem = "\
R75,D30,R83,U83,L12,D49,R71,U7,L72
U62,R66,U55,R34,D71,R55,D58,R83"
            .parse()
            .unwrap();

        assert_eq!(solve_part_2(&p), Some(610));
    }

    #[test]
    fn test_solve_part2_3() {
        let p: Problem = "\
R98,U47,R26,D63,R33,U87,L62,D20,R33,U53,R51
U98,R91,D20,R16,D67,R40,U7,R15,U6,R7"
            .parse()
            .unwrap();

        assert_eq!(solve_part_2(&p), Some(410));
    }
}
