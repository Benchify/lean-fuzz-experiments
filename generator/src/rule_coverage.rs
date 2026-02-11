//! Grammar rule coverage tracking for coverage-guided fuzzing.
//!
//! Tracks which grammar rules produce interesting outcomes (code that compiles,
//! reaches verifiers, etc.) to guide mutation toward productive rules.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

/// Outcome of executing a test case
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// Code failed to compile (lake build failed)
    Failed,
    /// Code compiled but failed verifiers
    CompiledOnly,
    /// Code compiled and passed comparator but not safeverify
    PassedComparator,
    /// Code compiled and passed both verifiers (jackpot!)
    PassedBoth,
}

impl Outcome {
    /// Is this outcome interesting enough to boost the rules that produced it?
    pub fn is_interesting(&self) -> bool {
        matches!(
            self,
            Outcome::CompiledOnly | Outcome::PassedComparator | Outcome::PassedBoth
        )
    }

    /// Priority score (higher = more interesting)
    pub fn priority(&self) -> u32 {
        match self {
            Outcome::Failed => 0,
            Outcome::CompiledOnly => 1,
            Outcome::PassedComparator => 5,
            Outcome::PassedBoth => 10,
        }
    }
}

/// Statistics for a single grammar rule
#[derive(Debug, Default)]
pub struct RuleStats {
    /// Total times this rule was used
    pub total_uses: AtomicUsize,
    /// Times this rule was in an input that compiled
    pub compiled_count: AtomicUsize,
    /// Times this rule was in an input that passed comparator
    pub comparator_count: AtomicUsize,
    /// Times this rule was in an input that passed both verifiers
    pub both_count: AtomicUsize,
}

impl RuleStats {
    /// Success rate (0.0 to 1.0) - fraction of uses that compiled
    pub fn success_rate(&self) -> f64 {
        let total = self.total_uses.load(Ordering::Relaxed);
        if total == 0 {
            return 0.0;
        }
        let compiled = self.compiled_count.load(Ordering::Relaxed);
        compiled as f64 / total as f64
    }

    /// Hotness score (higher = more valuable for fuzzing)
    pub fn hotness(&self) -> f64 {
        let total = self.total_uses.load(Ordering::Relaxed);
        if total < 5 {
            // Need at least 5 samples before we trust the stats
            return 1.0;
        }

        let compiled = self.compiled_count.load(Ordering::Relaxed);
        let comparator = self.comparator_count.load(Ordering::Relaxed);
        let both = self.both_count.load(Ordering::Relaxed);

        // Weighted score: compilation is good, verifier passes are better
        let score = compiled as f64 + comparator as f64 * 5.0 + both as f64 * 10.0;
        score / total as f64
    }
}

/// Tracks which grammar rules produce interesting outcomes
pub struct RuleCoverage {
    /// Stats per rule name (e.g., "THEOREM_DECL", "INDUCTIVE_DECL")
    rules: Mutex<HashMap<String, RuleStats>>,
    /// Number of executions tracked
    total_executions: AtomicUsize,
}

impl RuleCoverage {
    pub fn new() -> Self {
        Self {
            rules: Mutex::new(HashMap::new()),
            total_executions: AtomicUsize::new(0),
        }
    }

    /// Record that these rules were used and produced the given outcome
    pub fn record(&self, rules_used: &[String], outcome: Outcome) {
        self.total_executions.fetch_add(1, Ordering::Relaxed);

        let mut map = self.rules.lock().unwrap();
        for rule in rules_used {
            let stats = map.entry(rule.clone()).or_default();
            stats.total_uses.fetch_add(1, Ordering::Relaxed);

            match outcome {
                Outcome::Failed => {}
                Outcome::CompiledOnly => {
                    stats.compiled_count.fetch_add(1, Ordering::Relaxed);
                }
                Outcome::PassedComparator => {
                    stats.compiled_count.fetch_add(1, Ordering::Relaxed);
                    stats.comparator_count.fetch_add(1, Ordering::Relaxed);
                }
                Outcome::PassedBoth => {
                    stats.compiled_count.fetch_add(1, Ordering::Relaxed);
                    stats.comparator_count.fetch_add(1, Ordering::Relaxed);
                    stats.both_count.fetch_add(1, Ordering::Relaxed);
                }
            }
        }
    }

    /// Get hotness score for a rule (for weighted mutation)
    pub fn get_hotness(&self, rule: &str) -> f64 {
        let map = self.rules.lock().unwrap();
        map.get(rule).map_or(1.0, |stats| stats.hotness())
    }

    /// Get the top N hottest rules
    pub fn top_rules(&self, n: usize) -> Vec<(String, f64)> {
        let map = self.rules.lock().unwrap();
        let mut scored: Vec<_> = map
            .iter()
            .map(|(name, stats)| (name.clone(), stats.hotness()))
            .collect();
        scored.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        scored.into_iter().take(n).collect()
    }

    /// Get rules that have never produced anything interesting (candidates for removal)
    pub fn cold_rules(&self, min_uses: usize) -> Vec<String> {
        let map = self.rules.lock().unwrap();
        map.iter()
            .filter(|(_, stats)| {
                let uses = stats.total_uses.load(Ordering::Relaxed);
                let compiled = stats.compiled_count.load(Ordering::Relaxed);
                uses >= min_uses && compiled == 0
            })
            .map(|(name, _)| name.clone())
            .collect()
    }

    /// Print a coverage report
    pub fn print_report(&self, top_n: usize) {
        let total = self.total_executions.load(Ordering::Relaxed);
        if total == 0 {
            return;
        }

        println!("\n📊 Grammar Rule Coverage Report");
        println!("Total executions: {}", total);

        let top = self.top_rules(top_n);
        if !top.is_empty() {
            println!("\n🔥 Hottest {} rules:", top_n);
            for (i, (rule, score)) in top.iter().enumerate() {
                let map = self.rules.lock().unwrap();
                if let Some(stats) = map.get(rule) {
                    let uses = stats.total_uses.load(Ordering::Relaxed);
                    let compiled = stats.compiled_count.load(Ordering::Relaxed);
                    let success_rate = stats.success_rate() * 100.0;
                    println!(
                        "  {}. {} (score: {:.2}, uses: {}, compiled: {}, success: {:.1}%)",
                        i + 1,
                        rule,
                        score,
                        uses,
                        compiled,
                        success_rate
                    );
                }
            }
        }

        let cold = self.cold_rules(10);
        if !cold.is_empty() {
            println!("\n❄️  Cold rules (never compiled, 10+ uses): {}", cold.len());
            for rule in cold.iter().take(5) {
                let map = self.rules.lock().unwrap();
                if let Some(stats) = map.get(rule) {
                    let uses = stats.total_uses.load(Ordering::Relaxed);
                    println!("  - {} ({} uses)", rule, uses);
                }
            }
            if cold.len() > 5 {
                println!("  ... and {} more", cold.len() - 5);
            }
        }
    }
}

impl Default for RuleCoverage {
    fn default() -> Self {
        Self::new()
    }
}
