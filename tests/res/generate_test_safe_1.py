import json
import sys

def generate_binary_hypercube(n):
    num_states = 2**n
    states = list(range(num_states))
    actions = [0]
    transitions = []
    for state in range(num_states):
        binary = format(state, f'0{n}b')
        for pos in range(n):
            new_binary = list(binary)
            new_binary[pos] = '1' if binary[pos] == '0' else '0'
            new_state = int(''.join(new_binary), 2)
            transitions.append([state, 0, new_state])
    
    labelling = {}
    for state in range(num_states):
        binary = format(state, f'0{n}b')
        labels = []
        for i in range(n):
            if binary[i] == '1':
                labels.append(f'b_{i}')
        labelling[str(state)] = labels


    state_0_formula = {"and": [ { "not": {"atom": f"b_{i}"} } for i in range(n)]}
    
    no_odd_cycle = {
        "name": "only odd length cycle",
        "regularsafety": {
            "acceptance": "nfa",
            "states": [
                0,
                1,
                2,
                3,
            ],
            "atomic_propositions": [
                *("b_" + str(i) for i in range(n))
                ],
            "edges": [
                {
                    "start": 0,
                    "actions": state_0_formula,
                    "destination": 1
                },
                {
                    "start": 1,
                    "actions": { "not": state_0_formula },
                    "destination": 2
                },
                {
                    "start": 2,
                    "actions": { "not": state_0_formula },
                    "destination": 1
                },
                {
                    "start": 1,
                    "actions": state_0_formula,
                    "destination": 3
                },
            ],
            "initial_states": [0],
            "accepting_states": [3],

        },
        "is_true": True
    }
    
    model = {
        "name": f"Binary hypercube with {n} bits",
        "lts": {
            "states": states,
            "actions": actions,
            "transitions": transitions,
            "initial_states": [0],
            "labelling": labelling
        },
        "properties": [no_odd_cycle]
    }
    return model


if __name__ == "__main__":
    N = 16 if len(sys.argv) < 2 else int(sys.argv[1])
    model = generate_binary_hypercube(N)
    with open("./tests/res/test_safe_1.gntmc", 'w') as f:
        json.dump(model, f, indent=2)
