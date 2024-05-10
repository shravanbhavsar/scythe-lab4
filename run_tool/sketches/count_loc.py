'''This script takes a directory as input and counts the number of lines of code
in each file. It then prints these values to the console.
'''

import os
from pprint import pprint

def count_file(fname):
    '''Count the number of lines of code in a file.

    Args:
        fname (str): The name of the file to count.

    Returns:
        int: The number of lines of code in the file. 
        int: The number of lines of code in the file between <properties> tags. 
        Both counts exclude comments.
    '''
    with open(fname, 'r') as f:
        lines = list(f.readlines())
    count_all = 0
    for line in lines:
        line = line.strip()
        # if line != "" and not line.startswith('\\*'):
        if not line.startswith('\\*'):
            count_all += 1
    count_properties = 0
    between_properties = False
    # print(lines[0].strip())
    for line in lines:
        line = line.strip()
        if line.startswith("\\* <properties>"):
            between_properties = True
        elif line.startswith("\\* </properties>"):
            between_properties = False
        if between_properties and line != "" and not line.startswith('\\*'):
            # print("SUCC", line, between_properties, line != "", not line.startswith('\\*'))
            count_properties += 1
        else:
            pass
            # print("FAIL", line, between_properties, line != "", not line.startswith('\\*'))
    # print(count_all, count_properties)
    # print("\n\n\n\n\n")
    return count_all, count_properties

def count_loc(directory):
    '''Count the number of lines of code in each file in a directory.

    Args:
        directory (str): The name of the directory to count.

    Returns:
        dict: A dictionary where the keys are the filenames and the values are
        the number of lines of code in the file.
    '''
    locs = {}
    exclude = [
        "raft_reconfig", "lamport_clocks", "sharded_kv_unmod", 
        "array_2pc", "sharded_kv_fail"]
    exclude = [f"{e}.tla" for e in exclude]
    # pprint(list(os.walk(directory)))
    for root, _, files in os.walk(directory):
        # print(root, files)
        for file in files:
            if (
                file.endswith('.tla') 
                and "sketch" not in file 
                and file not in exclude
                and "legacy" not in root
                    ):
                path = os.path.join(root, file)
                count_all, count_properties = count_file(path)
                # print(path, count_all, count_properties)
                locs[file] = count_all, count_properties
    return locs

if __name__ == '__main__':
    # use the current directory as the default
    directory = os.getcwd()
    locs = count_loc(directory)
    for file, count in locs.items():
        print(f'{file}: {count[0]} lines of code, {count[1]} lines of code between <properties> tags')