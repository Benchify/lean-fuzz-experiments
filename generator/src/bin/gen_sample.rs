use clap::Parser;
use generator::{create_context, create_prefix_context, generate_one, NautilusInput};
use libafl::generators::nautilus::NautilusGenerator;
use libafl::generators::Generator;
use libafl::state::NopState;

#[derive(Parser)]
#[command(about = "Generate a random Lean 4 code sample from the grammar")]
struct Cli {
    /// Nautilus tree depth (higher = deeper nesting)
    #[arg(default_value_t = 15)]
    depth: usize,

    /// Use prefix-only grammar (no proof terms/tactics, theorems use sorry)
    #[arg(long)]
    prefix_only: bool,
}

fn main() {
    let cli = Cli::parse();
    let ctx = if cli.prefix_only {
        create_prefix_context(cli.depth)
    } else {
        create_context(cli.depth)
    };
    let mut generator = NautilusGenerator::new(&ctx);
    let mut state: NopState<NautilusInput> = NopState::new();
    let input = generator.generate(&mut state).expect("generation failed");
    print!("{}", generate_one(&ctx, &input));
}
