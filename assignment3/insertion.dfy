method insertionSort(a : array<nat>)
    modifies a
{
    var i := 0;
    var  key, j;
    while (i < a.Length)
    {
        print("OUTER\n");
        var idx := 0;
        while(idx < a.Length)
        {
            print(a[idx]);
            idx := idx + 1;
        }
        print("\nOUTER\n");
        key := a[i];
        j := i - 1;
        while (j >= 0 && a[j] > key)
        {
            a[j + 1] := a[j];
            a[j] := key;
            j := j - 1;
            var x := 0;
            print("i = ");
            print(i);
            print(", j = ");
            print(j);
            print("\n");
            while(x < a.Length)
            {
                print(a[x]);
                x := x + 1;
            }
            print("\n");
        }
        print("\n");
        //a[j + 1] := key;
        i := i + 1;
    }
}

// Input Space
datatype InputSpace = InputSpace(a:array<nat>)

// State Space
datatype StateSpace = StateSpace(a:array<nat>, bubbleIdx:nat)

predicate sorted(state: StateSpace, begin: int, end: int)
    reads state.a
    requires state.a.Length > 0
{
    forall i, j :: 0 <= begin <= i <= j <= end < state.a.Length ==> state.a[i] <= state.a[j]
}

predicate bubbled(state: StateSpace, bubbleIdx: int)
    reads state.a
    requires state.a.Length > 0
{
    forall i, j :: 0 <= i <= bubbleIdx < j < state.a.Length ==> state.a[i] <= state.a[j]
}


method insertionSortTransitionSystem(initialState : StateSpace) returns (terminalState:StateSpace)
    modifies initialState.a
    //requires initialState.a.Length > 0
    //ensures terminalState.a.Length > 0
    //ensures sorted(terminalState, 0, terminalState.a.Length - 1)
{
    var i := 0;
    var  key, j;
    while (i < initialState.a.Length)
    {
        key := initialState.a[i];
        j := i - 1;
        while (j >= 0 && initialState.a[j] > key)
        {
            initialState.a[j + 1] := initialState.a[j];
            initialState.a[j] := key;
            j := j - 1;
        }
        //a[j + 1] := key;
        i := i + 1;
    }
    terminalState := initialState;
    return terminalState;
}

// Orchestrator
method Main()
{
    var arr := new nat[5];
    arr[0] := 5;
    arr[1] := 4;
    arr[2] := 3;
    arr[3] := 2;
    arr[4] := 1;
    //var inputParameters := InputSpace(arr);
    var initialState := StateSpace(arr, 4);
    var terminalState := insertionSortTransitionSystem(initialState);
    var output := terminalState.a;
    //assert sorted(StateSpace(output, output.Length - 1), 0, output.Length - 1) == true;
    //insertionSort(arr);
    var x := 0;
    while(x < output.Length)
    {
        print(output[x]);
        x := x + 1;
    }
}
