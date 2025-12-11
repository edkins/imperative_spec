use clap::Parser;

mod check;
mod syntax;
mod type_inference;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Input file to process (or directory name to test)
    input_file: String,
    /// Verbose output
    #[arg(short, long, default_value_t = false)]
    verbose: bool,
}

fn check_dir(dir: &str) {
    let mut skip = false;
    let mut success = true;
    for entry in std::fs::read_dir(dir).expect("Failed to read directory") {
        let entry = entry.expect("Failed to read directory entry");
        let path = entry.path();
        if path.is_file() {
            let input = std::fs::read_to_string(&path).expect("Failed to read file");
            println!("Checking file: {}", path.display());
            let source_file = syntax::parse::parse_source_file(&input);
            if source_file.is_err() {
                println!("❌  Failed to parse file: {}", path.display());
                success = false;
                println!();
                continue;
            }
            let source_file = source_file.unwrap();
            let p = std::path::Path::new(&path);
            if p.file_name().unwrap().to_str().unwrap().ends_with(".zzz") {
                println!("⬇️  Skipping .zzz file");
                skip = true;
                println!();
                continue;
            }
            if p.file_name().unwrap().to_str().unwrap().starts_with("f_") {
                match check::z3check::z3_check(&source_file, 0) {
                    Ok(_) => {
                        println!("❌  Check unexpectedly succeeded");
                        success = false;
                    }
                    Err(_) => {
                        println!("✅  Check failed as expected");
                    }
                }
            } else {
                match check::z3check::z3_check(&source_file, 0) {
                    Err(e) => {
                        println!("❌  Check failed: {}", e);
                        success = false;
                    }
                    Ok(_) => {
                        println!("✅  Check succeeded");
                    }
                }
            }
            println!();
        }
    }
    if success {
        if skip {
            println!("⚠️  Some files were skipped");
        } else {
            println!("✅✅✅ All checks passed");
        }
    } else {
        println!("❌❌❌ Some checks failed");
    }
}

fn main() {
    let args = Args::parse();

    if std::fs::metadata(&args.input_file)
        .expect("Failed to get metadata")
        .is_dir()
    {
        check_dir(&args.input_file);
        return;
    }

    let input = std::fs::read_to_string(&args.input_file).expect("Failed to read input file");
    let source_file = syntax::parse::parse_source_file(&input).expect("Failed to parse input file");
    println!("{}", source_file);
    println!("-------");
    check::z3check::z3_check(&source_file, if args.verbose { 2 } else { 1 })
        .expect("Failed to check function");
}
