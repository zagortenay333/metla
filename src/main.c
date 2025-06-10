#include "base/core.h"
#include "base/mem.h"
#include "base/array.h"
#include "os/fs.h"
#include "compiler/x64.h"

istruct (CmdLine) {
    U64 cursor;
    Slice(CString) args;
    String main_file_path;
};

static Void cli_print_options () {
    printf(
        "-h        Print command line options.\n"
        "-i <path> File path of main file.\n"
    );
}

static String cli_eat (CmdLine *cli, CString error_msg) {
    String s;

    if (cli->cursor < cli->args.count) {
        s = str(array_get(&cli->args, cli->cursor));
        cli->cursor++;
    } else {
        s = (String){};
        log_msg_fmt(LOG_ERROR, "", 1, "%s", error_msg);
    }

    return s;
}

static CmdLine cli_parse (Int argc, CString *argv) {
    CmdLine cli = { .cursor=1, .args={ .data=argv, .count=cast(U64, argc) } };
    log_scope(ls, 1);

    while (cli.cursor < cli.args.count) {
        String arg = cli_eat(&cli, "");

        if (str_match(arg, str("-h"))) {
            cli_print_options();
        } else if (str_match(arg, str("-i"))) {
            cli.main_file_path = cli_eat(&cli, "Command line argument '-i' missing file operand.");
        } else {
            log_msg_fmt(LOG_ERROR, "", 1, "Unknown command line argument '%.*s'.", STR(arg));
        }

        if (ls->count[LOG_ERROR]) break;
    }

    if (cli.args.count == 1) cli_print_options();
    return cli;
}

Int main (Int argc, CString *argv) {
    random_setup();
    tmem_setup(mem_root, 1*MB);
    log_setup(mem_root, 4*KB);
    log_scope(ls, 1);

    CmdLine cli = cli_parse(argc, argv);
    x64_test(cli.main_file_path);
}
