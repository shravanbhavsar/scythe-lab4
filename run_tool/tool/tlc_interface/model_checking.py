from pprint import pprint
import tempfile
import random
import subprocess
import sys
import os
import logging
from pathlib import Path
import traceback
import shutil

from .violations import parse_violation


JAR_PATH = Path(__file__).parent.absolute() / "tla2tools-structured.jar"
# JAR_PATH = Path(__file__).parent.absolute() / "tla2tools-structured-v2.jar"

# TODO: spin up some kind of java server and query it, rather than
# running a new instance of the TLC jar every time?
# modified from endive
# https://github.com/will62794/endive/blob/master/endive.py
def runtlc(spec,tlc_workers=1,cwd=None,java="java",tlc_flags=""):
    # Make a best effort to attempt to avoid collisions between different
    # instances of TLC running on the same machine.
    tlc_workers = 8
    dirpath = tempfile.mkdtemp()
    metadir_dir = "/scratch/egolf.d/"
    # check if metadir_dir exists
    if not os.path.exists(metadir_dir):
        metadir_dir = ""
    metadir_path = f"states/states_{random.randint(0,1000000000)}"
    metadir_path = metadir_dir + metadir_path
    cmd = java + (f' -Djava.io.tmpdir="{dirpath}"' 
                  f' -cp {JAR_PATH}'
                  f' tlc2.TLC {tlc_flags}'
                  f' -metadir {metadir_path}'
                  f' -teSpecOutDir {dirpath}'
                  f' -noGenerateSpecTE'
                  f' -workers {tlc_workers}'
                  )
    cmd += " " + spec
    logging.info("TLC command: " + cmd)
    subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=cwd)
    line_str = ""
    tlc_lines = []
    while True:
        tmp = subproc.stdout
        if tmp is None:
            raise ValueError("TLC subprocess stdout is None")
        new_stdout = tmp.read(1).decode(sys.stdout.encoding)
        if new_stdout == "": # reached end of file.
            break
        if new_stdout == os.linesep:
            logging.debug("[TLC Output] " + line_str)
            tlc_lines.append(line_str)
            line_str = ""
        else:
            line_str += new_stdout
    return tlc_lines


def model_check(name : str, spec : str, config : str, params_map : dict):
    # write the spec to a temporary file
    dirpath = tempfile.mkdtemp()
    specpath = Path(dirpath) / f"{name}.tla"
    with open(specpath, "w") as f:
        f.write(spec)
    # write the config to a temporary file
    configpath = Path(dirpath) / f"{name}.cfg"
    with open(configpath, "w") as f:
        f.write(config)

    support_dir = Path(__file__).parent          # repo folder
    for mod in ["Voting.tla", "TLAPS.tla", "Consensus.tla", "FiniteSetTheorems.tla", "Functions.tla", "WellFoundedInduction.tla", "NaturalsInduction.tla"]:                   # add more as strings
        shutil.copy(support_dir / mod, dirpath)

    # run TLC
    count = 0
    while True:
        count += 1
        tlc_lines = runtlc(str(specpath))
        # With low probability, TLC throws an unexpected exception.
        # We retry upto three times.
        try:
            violation = parse_violation(tlc_lines, params_map)
            break
        except RuntimeError as e:
            tb = traceback.format_exc()
            print(tb)
            if len(e.args) == 0:
                raise e
            msg = e.args[0]
            if "unexpected" not in msg:
                raise e
            if count > 3:
                raise e
    return violation
