method insertionSort(a : array<nat>)
    modifies a
{
    var i := 0;
    while (i < a.Length)
    {
        var j := i - 1;
        while (j >= 0 && a[j] > a[j + 1])
        {
            a[j], a[j + 1] := a[j + 1], a[j];
            j := j - 1;
        }
        i := i + 1;
    }
}

// Input Space
datatype InputSpace = InputSpace(a:array<nat>)

// State Space
datatype StateSpace = StateSpace(a:array<nat>, idx:nat)

predicate sorted(state: StateSpace, begin: int, end: int)
    reads state.a
    requires state.a.Length > 0
{
    forall i, j :: 0 <= begin <= i <= j <= end < state.a.Length ==> state.a[i] <= state.a[j]
}

method insertionSortTransitionSystem(initialState : StateSpace) returns (terminalState:StateSpace)
    modifies initialState.a
    requires initialState.a.Length > 0
    ensures terminalState.a.Length > 0
    ensures multiset(initialState.a[..]) == multiset(terminalState.a[..])
    ensures sorted(terminalState, 0, terminalState.a.Length - 1)
{
    var i := 0;
    while (i < initialState.a.Length)
        decreases initialState.a.Length - i
        invariant 0 <= i <= initialState.a.Length
        invariant sorted(initialState, 0, i - 1)
    {
        var j := i - 1;
        while (j >= 0 && initialState.a[j] > initialState.a[j + 1])
            invariant -1 <= j <= i - 1
            invariant forall k :: j + 1 < k <= i ==> initialState.a[j + 1] < initialState.a[k]
            invariant forall m, n :: 0 <= m <= j && j + 2 <= n <= i ==> initialState.a[m] <= initialState.a[n]
            invariant sorted(initialState, 0, j)
            invariant sorted(initialState, j + 2, i)
            decreases j
        {
            initialState.a[j], initialState.a[j + 1] := initialState.a[j + 1], initialState.a[j];
            j := j - 1;
        }
        i := i + 1;
    }
    assert sorted(initialState, 0, initialState.a.Length - 1);
    terminalState := initialState;
}

// Orchestrator
method Main()
{
    var arr := new nat[10];
    arr[0] := 9;
    arr[1] := 8;
    arr[2] := 7;
    arr[3] := 6;
    arr[4] := 5;
    arr[5] := 4;
    arr[6] := 3;
    arr[7] := 2;
    arr[8] := 1;
    arr[9] := 0;
    var inputParameters := InputSpace(arr);
    var initialState := StateSpace(arr, 4);
    var terminalState := insertionSortTransitionSystem(initialState);
    var output := terminalState.a;
    assert sorted(StateSpace(output, output.Length - 1), 0, output.Length - 1);
    insertionSort(arr);
    var x := 0;
    while(x < output.Length)
    {
        print(output[x]);
        x := x + 1;
    }
    print("\n");
    x := 0;
    while(x < arr.Length)
    {
        print(arr[x]);
        x := x + 1;
    }
}
