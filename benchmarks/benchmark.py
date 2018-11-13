import os
import sys

start_string = "_toplevel:\n"
end_string = "\tb\t_toplevel_ret\n"

c_start_string = "int main(){\n"
c_end_string = "return 0;\n"

start_timer_string = "\tbl\tstart_timer\n"
stop_timer_string = "\tbl\tstop_timer\n"

c_start_timer_string = "\tclock_t begin = clock();\n"
c_stop_timer_string = """
    clock_t end = clock();
    double time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
    printf("cpu time:\t%f seconds\\n", time_spent);
    """


def append_timer(filename):
    ret = []
    start_timing = -1
    with open(filename, "r") as f:
        buf = f.readlines()
    for i, line in enumerate(buf):
        if line == start_string:
            ret.append(line)
            start_timing = i + 4
        elif i == start_timing:
            ret.append(line)
            ret.append(start_timer_string)
        elif line == end_string:
            ret.append(stop_timer_string)
            ret.append(line)
        else:
            ret.append(line)
    with open(filename, "w") as f:
        for l in ret:
            f.write(l)


def append_c_timer(filename):
    ret = []
    with open(filename, "r") as f:
        buf = f.readlines()
    buf = ["#include <time.h>\n"] + buf
    for i, line in enumerate(buf):
        if line == c_start_string:
            ret.append(line)
            ret.append(c_start_timer_string)
        elif line == c_end_string:
            ret.append(c_stop_timer_string)
            ret.append(line)
        else:
            ret.append(line)
    with open(filename, "w") as f:
        for l in ret:
            f.write(l)


def make_command(inname, outname, is_arm, is_reg, is_opt):
    base = "./minimlc -i %s -o %s" % (inname, outname)
    if not is_arm:
        base += " -b "
    if is_reg:
        base += " -reg"
    if is_opt:
        base += " -O"
    print("executing %s" % base)
    return base


def run(inname, outname, is_arm, is_reg, is_opt):
    command = make_command(inname, outname, is_arm, is_reg, is_opt)
    os.system(command)
    if is_arm:
        append_timer(outname)
        os.system("gcc -o tmp lib/main.c lib/timer.s %s" % outname)
        os.system("./tmp")
    else:
        append_c_timer(outname)
        os.system("gcc %s" % outname)
        os.system("./a.out")


def main():
    if sys.argv[1]:
        in_file = sys.argv[1]
        in_name = os.path.splitext(os.path.basename(in_file))[0]
        run(in_file, "%s_opt.c" % in_name, False, False, True)
        run(in_file, "%s_no_opt.c" % in_name, False, False, False)
        run(in_file, "%s_noreg_noopt_.s" % in_name, True, False, False)
        run(in_file, "%s_noreg_opt.s" % in_name, True, False, True)
        run(in_file, "%s_reg_noopt.s" % in_name, True, True, False)
        run(in_file, "%s_reg_opt.s" % in_name, True, True, True)


if __name__ == "__main__":
    main()

