# Rerunning Experiments

## Setup

The tool was tested using Python 3.9.13 (run `python --version` to check your
version). Install the following python packages:

* sympy
* call_function_with_timeout
* sexpdata

### Check TLC

navitgate to [./sketches/](./sketches/) and run the following command to confirm
TLC is installed.

```
java -cp tla2tools-structured.jar tlc2.TLC simple_decentralized_lock.tla
```

The output should end in something like

```
Model checking completed. No error has been found.
Estimates of the probability that TLC did not check all reachable states
because two distinct states had the same fingerprint:
calculated (optimistic):  val = 5.9E-18
21 states generated, 12 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 2.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 3 and the 95th perc
entile is 3).
Finished in 00s at (2024-05-10 09:41:11)
```

If you obtain any errors, check your java version: `java --version`

I see the following output when running the above.

```
openjdk 17.0.7 2023-04-18
OpenJDK Runtime Environment (build 17.0.7+7-Ubuntu-0ubuntu118.04)
OpenJDK 64-Bit Server VM (build 17.0.7+7-Ubuntu-0ubuntu118.04, mixed mode, sharing)
```

### Check the tool

Run the following quick, test experiment. It should terminate in a few seconds.
Otherwise install any missing dependencies.

```
python benchmark.py configs.json 0 1
```

The output should end in something resembling

```
Summary:
  Timing:
    Total: 1.592815637588501
    Model checking: 1.586364507675171
  Generated:
    # candidates model checked: 1
    # Candidates eliminated before model checking: 0
 Solution at: see run_tool/README.md
```


## Rerunning Experiments

To rerun  experiment from the table use the command

```
python benchmark.py configs.json <table ID> <0|1>
```

Where `table ID` is the number from the ID column in Table I of the paper. If
the final argument is 0 (resp. 1), the tool is run without (resp. with) the
equivalence reduction. See section Check the tool for an example command.

## Viewing Synthesized Solutions after Rerunning

Navigate to
[../discovery_output_data/solutions/](../discovery_output_data/solutions/) to
find the synthesized solution for the last experiment. For instance, if the
experiment has ID 3, look at `0_3_0.tla`.

## Sketches

Sketches can be found in [./sketches/](./sketches/). For protocol `protocol`,
the relevant files are (1) `protocol_sketch.tla` that contains the sketch w/o
any grammars and (2) `protocol_grams.py` where the grammar generating scripts
are located.