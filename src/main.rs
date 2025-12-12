use std::path::Path;

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

fn all_checks(path: &Path, verbosity: u8) -> Result<(), String> {
    let input = std::fs::read_to_string(path).map_err(|e| format!("Failed to read input file: {}", e))?;
    let mut source_file = syntax::parse::parse_source_file(&input)
        .map_err(|e| format!("Failed to parse input file: {}", e))?;
    type_inference::hm::hindley_milner_infer(&mut source_file, verbosity).map_err(|e| format!("Type inference failed: {}", e))?;
    Ok(())
}

fn check_dir(dir: &str) {
    let mut skip = false;
    let mut success = true;
    for entry in std::fs::read_dir(dir).expect("Failed to read directory") {
        let entry = entry.expect("Failed to read directory entry");
        let path = entry.path();
        if path.is_file() {
            if path.file_name().unwrap().to_str().unwrap().ends_with(".zzz") {
                println!("⬇️  Skipping .zzz file");
                skip = true;
                println!();
                continue;
            }
            println!("Checking file: {}", path.display());
            let result = all_checks(&path, 0);
            if path.file_name().unwrap().to_str().unwrap().starts_with("f_") {
                match result {
                    Ok(_) => {
                        println!("❌  Check unexpectedly succeeded");
                        success = false;
                    }
                    Err(_) => {
                        println!("✅  Check failed as expected");
                    }
                }
            } else {
                match result {
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

    all_checks(Path::new(&args.input_file), if args.verbose { 2 } else { 1 }).expect("Failed to process file");
}
