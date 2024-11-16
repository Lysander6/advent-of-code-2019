use day_01::add;

fn main() -> Result<(), anyhow::Error> {
    println!("Hello, World! {}", add(2, 3));

    Ok(())
}
