#define NOB_IMPLEMENTATION
#include "nob.h"

int main(int argc, char** argv) {
    NOB_GO_REBUILD_URSELF(argc, argv);

    Nob_Cmd cmd = {0};
    // basic stuff
    nob_cmd_append(&cmd, "cc");
    nob_cmd_append(
        &cmd, "-Wall", "-Wextra", "-std=c11",
        /* "-ggdb", "-fsanitize=address", "-fsanitize=leak" */
    );
    // linking
    nob_cmd_append(&cmd, "-lreadline", "-lm");
    // output
    nob_cmd_append(&cmd, "-o", "calc");
    nob_cmd_append(&cmd, "calc.c");

    if (!nob_cmd_run_sync(cmd)) {
        nob_cmd_free(cmd);
        return 1;
    }

    // run executable
    cmd.count = 0;
    nob_cmd_append(&cmd, "./calc");
    if (!nob_cmd_run_sync(cmd)) {
        nob_cmd_free(cmd);
        return 1;
    }

    nob_cmd_free(cmd);
    return 0;
}
