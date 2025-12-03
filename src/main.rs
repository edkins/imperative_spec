use clap::Parser;

mod check;
mod syntax;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Input file to process (or directory name to test)
    input_file: String,
}

fn check_dir(dir: &str) -> Result<(), Box<dyn std::error::Error>> {
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_file() {
            let input = std::fs::read_to_string(&path)?;
            println!("Checking file: {}", path.display());
            let source_file = syntax::parse::parse_source_file(&input)?;
            let p = std::path::Path::new(&path);
            if p.file_name().unwrap().to_str().unwrap().ends_with(".zzz") {
                println!("  Skipping .zzz file");
                continue;
            }
            if p.file_name().unwrap().to_str().unwrap().starts_with("f_") {
                match check::z3check::z3_check(&source_file) {
                    Ok(_) => {
                        return Err(Box::new(std::io::Error::new(
                            std::io::ErrorKind::Other,
                            format!("Expected check to fail for file: {}", path.display()),
                        )));
                    }
                    Err(e) => {
                        println!("  Check failed as expected: {}", e);
                    }
                }
            } else {
                check::z3check::z3_check(&source_file)?;
            }
        }
    }
    Ok(())
}

fn main() {
    let args = Args::parse();

    if std::fs::metadata(&args.input_file)
        .expect("Failed to get metadata")
        .is_dir()
    {
        check_dir(&args.input_file).expect("Failed to check directory");
        return;
    }

    let input = std::fs::read_to_string(&args.input_file).expect("Failed to read input file");
    let source_file = syntax::parse::parse_source_file(&input).expect("Failed to parse input file");
    println!("{}", source_file);
    check::z3check::z3_check(&source_file).expect("Failed to check function");
}
