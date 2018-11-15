import os
import sys


def run(p, filename):
    command = "./minimlc -i %s -s" % os.path.join(p, filename)
    print("running %s" % command)
    os.system(command)


def run_mult(path):
    for test_file in os.listdir(path)[:4]:
        run(path, test_file)


def main():
    p = sys.argv[1]
    run_mult(p)
    print("completed")


if __name__ == "__main__":
    main()
