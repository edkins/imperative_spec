use clap::Parser;

mod check;
mod syntax;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Input file to process
    input_file: String,
}

fn main() {
    let args = Args::parse();
    let input = std::fs::read_to_string(&args.input_file)
        .expect("Failed to read input file");
    let source_file = syntax::parse::parse_source_file(&input)
        .expect("Failed to parse input file");
    println!("{}", source_file);
    check::z3check::z3_check(&source_file)
        .expect("Failed to check function");
}
