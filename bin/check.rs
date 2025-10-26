use json_parser::{parse, tokenize};
use std::env;

fn main() {
    let args: Vec<_> = env::args().collect();
    if args.len() != 2 {
        println!("Usage: {} file.json", args[0]);
        std::process::exit(1);
    }

    let ref path = args[1];
    let contents = std::fs::read_to_string(path).unwrap();
    let tokens = parse(&contents).unwrap();
    println!("{}", tokens);
    // let tokens = tokenize(&contents);
}
