class HashMap{
    ghost var ghostMapa: map<int,char>;
    var arraySize : int;
    var currentNumberOfElem : int;
    var mapa : array<seq<(int, char)>>;

    function repInv() : bool
      reads this, mapa;
    {
        arraySize > 0
      
        && 0 <= currentNumberOfElem <= arraySize
        && mapa.Length == arraySize
        && forall i :: 0 <= i < arraySize ==> |mapa[i]| <= currentNumberOfElem
        //&& forall i :: 0 <= i < arraySize ==> forall j:: 0 <= j < |mapa[i]| ==> mapa[i][j].0 % arraySize == i
        && forall i :: 0 <= i < arraySize ==> forall j, k :: 0 <= j < k < |mapa[i]| ==> mapa[i][j].0 != mapa[i][k].0
        

    }

    function sound() : bool
      requires repInv()
      reads this, mapa

      { 

        currentNumberOfElem == |ghostMapa| &&
        forall x :: x in ghostMapa ==> exists j :: 0 <= j < |mapa[x % arraySize]| && mapa[x % arraySize][j].0 == x
        && mapa[x % arraySize][j].1 == ghostMapa[x]

      }

    function checkEverything() :bool
      reads this, mapa
    {
      repInv() && sound()
    }


    constructor(s:int)
      requires s > 0;
      ensures checkEverything();
      ensures isEmpty();

    {
        arraySize := s;
    

        currentNumberOfElem := 0;

        var sequence := new seq<(int, char)>[s];
        var i := 0;

        while (i < s)
        decreases s - i
        invariant 0 <= i <= s
        invariant forall k :: 0<= k < i ==> |sequence[k]| == 0

        {
          sequence[i] := [];
          i := i + 1;
        }

        mapa := sequence;

        ghostMapa := map[];

    }

    function isEmpty() : bool
      reads this, mapa
      requires checkEverything()
    {
        currentNumberOfElem == 0 && |ghostMapa| == 0
    }

    function isFull() : bool
      reads this, mapa
      requires checkEverything()
    {
        currentNumberOfElem == arraySize
    }

    function hashFunction(k:int) : int

      reads this, mapa
      requires checkEverything()
    {
        k % arraySize
    }

    method hash(k:int) returns (h:int)

      requires checkEverything();
      ensures h == hashFunction(k)
    {
        h := k % arraySize;
    }

    method put(k:int, v:char)

      modifies mapa, `currentNumberOfElem, `ghostMapa
      requires k > 0
      requires checkEverything()
      requires !isFull()
      
      
      //ensures forall  i:: 0 <= i < arraySize ==> |mapa[i]| >= old(|mapa[i]|)
      
      // ensures currentNumberOfElem == old(currentNumberOfElem) + 1 <== |mapa[hashFunction(k)]| > 0
        
      //   && mapa[hashFunction(k)][ |mapa[hashFunction(k)]| - 1] == (k,v)
      //   && old(mapa[hashFunction(k)]) != mapa[hashFunction(k)]

      // ensures forall i:: 0 <= i < arraySize ==> forall j :: 0 <= j < |old(mapa[i])| ==> old(mapa[i][j]) == mapa[i][j]
      
      // ensures old(mapa[hashFunction(k)]) == mapa[hashFunction(k)] <== exists j :: 0 <= j < old(|mapa[hashFunction(k)]|) 
      //   && old(mapa[hashFunction(k)][j].0) == k
      

      ensures currentNumberOfElem == old(currentNumberOfElem) + 1 ==> k !in old(ghostMapa);
      ensures checkEverything()
      ensures !isEmpty()

      ensures k in ghostMapa;
      //ensures if k in old(ghostMapa) then ghostMapa == old(ghostMapa) else ghostMapa == old(ghostMapa)[k := v]
      {

      var index := hash(k);

        if(!(exists j :: 0 <= j < |mapa[index]| && mapa[index][j].0 == k)){

          //assert(k in ghostMapa);

          
          ghostMapa := ghostMapa[k := v];

          mapa[index] := mapa[index] + [(k, v)];

          currentNumberOfElem := currentNumberOfElem + 1;

          assert(k in ghostMapa);

          
        }
      }

    method get(k:int, def:char) returns(v:char)

      requires k > 0
      requires checkEverything()
      ensures checkEverything()


      //ensures v == def <==> |mapa[hashFunction(k)]| == 0 || (forall j :: 0 <= j < |mapa[hashFunction(k)]| ==> mapa[hashFunction(k)][j].0 != k)
      //|| (exists j :: 0 <= j < |mapa[hashFunction(k)]| && mapa[hashFunction(k)][j].0 == k && mapa[hashFunction(k)][j].1 == def)

      ensures v != def <== k in ghostMapa && ghostMapa[k] != def
      ensures v == def ==> k !in ghostMapa || ghostMapa[k] == def
    {

    var index := hash(k);

    if(|mapa[index]| != 0) {

        var i:int := 0;

        while(i < |mapa[index]|)
        
        decreases |mapa[index]| - i
        invariant |mapa[index]| >= i >= 0
        invariant forall j :: 0 <= j < i ==> mapa[index][j].0 != k

        {

          if(mapa[index][i].0 == k){
            
            return mapa[index][i].1;
          
          }

          i := i +1;
        }
      }

    return def;

    }

    method contains(k:int) returns(z:bool)
      requires checkEverything()
      
      ensures checkEverything()
      ensures z == true <==> k in ghostMapa;
      ensures z == false <==> k !in ghostMapa;

    {

    var index := hash(k);


     if( |mapa[index]| != 0) {

        var i:int := 0;

        while(i < |mapa[index]|)

        decreases |mapa[index]| - i
        invariant |mapa[index]| >= i >= 0
        invariant forall j :: 0 <= j < i ==> mapa[index][j].0 != k

        {

          if(mapa[index][i].0 == k){
            
            return true;
          
          }

          i := i +1;
        }
      }

    return false;

    }
}