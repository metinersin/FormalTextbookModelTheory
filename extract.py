import os
import re

ALLOWED_TYPES = [
    "lemma",
    "theorem",
    "def",
    "class",
    "structure",
    "inductive",
    "namespace",
    "section",
]


def merge_consecutive_spaces(text):
    return re.sub(r"\s+", " ", text)


def get_type_and_name(line):
    tmp = line.split(" ")

    if len(tmp) == 1:
        return tmp[0], None

    return tmp[0], tmp[1]


def relevant(line):
    type, _ = get_type_and_name(line)
    return type in ALLOWED_TYPES


def trim(line):
    return merge_consecutive_spaces(line.strip())


def readlines_raw(path):
    try:
        with open(path, "r") as file:
            return file.readlines()
    except FileNotFoundError:
        raise FileNotFoundError(f"File '{path}' not found.")


def readlines_trimmed(path):
    try:
        with open(path, "r") as file:
            return [trim(line) for line in file.readlines()]
    except FileNotFoundError:
        raise FileNotFoundError(f"File '{path}' not found.")


def remove_irrelevant(lines):
    return [line for line in lines if relevant(line)]


def process(lines):
    data = [None for _ in lines]
    for i, line in enumerate(lines):
        data[i] = get_type_and_name(line)
    return data


def readlines_processed(path):
    lines = readlines_trimmed(path)
    lines = remove_irrelevant(lines)
    lines = process(lines)
    return lines


# def remove_namespace(lines):
#     mask = [True for _ in lines]
#     for i, line in enumerate(lines):
#         if re.match(start_with_namespace, line):
#             pass


# def remove_section(lines):
#     raise NotImplementedError


def main():
    # Read and print the content of the file
    path = os.path.join("ForMathlib", "Language.lean")

    lines = readlines_processed(path)
    for line in lines:
        print(line)


if __name__ == "__main__":
    main()
