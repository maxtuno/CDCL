# CDCL
 
A simple and pure CDCL algorithm for experiment with new heuristics, and evaluate some hypothesis from https://twitter.com/maxtuno (based on me basilisk sat solver)

Include the (simple) "VW Frequency Heuristic" [Oscar Riveros 2022].

    usage: cdcl <cnf-instance-file> [--all] [--drat-proof]

    --all: all solutions
    --drat-proof: generate the drat-proof check with drat-trim https://www.cs.utexas.edu/~marijn/drat-trim/