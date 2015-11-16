
import json
import argparse

if __name__ == '__main__':
    a = argparse.ArgumentParser()
    a.add_argument("filename", nargs="?", default="/tmp/prog.json")
    a = a.parse_args()

    f = open(a.filename)

    l = [json.loads(line) for line in f if line.strip()]

    for json in l:
        print json['text']
