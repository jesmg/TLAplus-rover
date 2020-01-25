------------------------------ MODULE RoverTLA ------------------------------

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS NROVERS, XFIELDSIZE, YFIELDSIZE

ASSUME NROVERS > 0
ASSUME XFIELDSIZE > NROVERS*2
ASSUME YFIELDSIZE > NROVERS*2

PositionInBounds(x, y) ==
    /\ x < XFIELDSIZE
    /\ x >= 0
    /\ y < YFIELDSIZE
    /\ y >= 0
    
NoOtherRoverCollision(x, y, xall, yall) == 
    ~\E otherRoverX \in DOMAIN xall:
        /\ ~\E otherRoverY \in DOMAIN yall:
           otherRoverX = otherRoverY
           /\ x = xall[otherRoverX]
           /\ y = yall[otherRoverY]
        
ThereIsObstacleColision ==
  CHOOSE x \in {TRUE, FALSE}: TRUE

(**--algorithm roverExploration
variables
    xPosition = [x \in 1..NROVERS |-> 0],
    yPosition = [y \in 1..NROVERS |-> 0],
    orientation = [ort \in 1..NROVERS |-> 0];

process Rover \in 1..NROVERS
  begin Mission:
    while TRUE do
      either
        Rotate:
          orientation[self] := CHOOSE x \in 0..3: TRUE;
      or    
        Move:
          if orientation[self] = 0 then         \* North
            if PositionInBounds(xPosition[self] + 1, yPosition[self]) 
              /\ NoOtherRoverCollision(xPosition[self] + 1, yPosition[self], xPosition, yPosition)
              /\ ~ThereIsObstacleColision
              then xPosition[self] := xPosition[self] + 1 end if;
          elsif orientation[self] = 1 then      \* East
            if PositionInBounds(xPosition[self], yPosition[self] + 1)
              /\ NoOtherRoverCollision(xPosition[self], yPosition[self] + 1, xPosition, yPosition)
              /\ ~ThereIsObstacleColision
              then yPosition[self] := yPosition[self] + 1 end if;
          elsif orientation[self] = 2 then       \* South
            if PositionInBounds(xPosition[self] - 1, yPosition[self])
              /\ NoOtherRoverCollision(xPosition[self] - 1, yPosition[self], xPosition, yPosition)
              /\ ~ThereIsObstacleColision
              then xPosition[self] := xPosition[self] - 1 end if;
          else                                   \* West
            if PositionInBounds(xPosition[self], yPosition[self] - 1)
              /\ NoOtherRoverCollision(xPosition[self], yPosition[self] - 1, xPosition, yPosition)
              /\ ~ThereIsObstacleColision
              then yPosition[self] := yPosition[self] - 1 end if;
          end if;
      end either;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES xPosition, yPosition, orientation, pc

vars == << xPosition, yPosition, orientation, pc >>

ProcSet == (1..NROVERS)

Init == (* Global variables *)
        /\ xPosition = [x \in 1..NROVERS |-> 0]
        /\ yPosition = [y \in 1..NROVERS |-> 0]
        /\ orientation = [ort \in 1..NROVERS |-> 0]
        /\ pc = [self \in ProcSet |-> "Mission"]

Mission(self) == /\ pc[self] = "Mission"
                 /\ \/ /\ pc' = [pc EXCEPT ![self] = "Rotate"]
                    \/ /\ pc' = [pc EXCEPT ![self] = "Move"]
                 /\ UNCHANGED << xPosition, yPosition, orientation >>

Rotate(self) == /\ pc[self] = "Rotate"
                /\ orientation' = [orientation EXCEPT ![self] = CHOOSE x \in 0..3: TRUE]
                /\ pc' = [pc EXCEPT ![self] = "Mission"]
                /\ UNCHANGED << xPosition, yPosition >>

Move(self) == /\ pc[self] = "Move"
              /\ IF orientation[self] = 0
                    THEN /\ IF  PositionInBounds(xPosition[self] + 1, yPosition[self])
                               /\ NoOtherRoverCollision(xPosition[self] + 1, yPosition[self], xPosition, yPosition)
                               /\ ~ThereIsObstacleColision
                               THEN /\ xPosition' = [xPosition EXCEPT ![self] = xPosition[self] + 1]
                               ELSE /\ TRUE
                                    /\ UNCHANGED xPosition
                         /\ UNCHANGED yPosition
                    ELSE /\ IF orientation[self] = 1
                               THEN /\ IF  PositionInBounds(xPosition[self], yPosition[self] + 1)
                                          /\ NoOtherRoverCollision(xPosition[self], yPosition[self] + 1, xPosition, yPosition)
                                          /\ ~ThereIsObstacleColision
                                          THEN /\ yPosition' = [yPosition EXCEPT ![self] = yPosition[self] + 1]
                                          ELSE /\ TRUE
                                               /\ UNCHANGED yPosition
                                    /\ UNCHANGED xPosition
                               ELSE /\ IF orientation[self] = 2
                                          THEN /\ IF  PositionInBounds(xPosition[self] - 1, yPosition[self])
                                                     /\ NoOtherRoverCollision(xPosition[self] - 1, yPosition[self], xPosition, yPosition)
                                                     /\ ~ThereIsObstacleColision
                                                     THEN /\ xPosition' = [xPosition EXCEPT ![self] = xPosition[self] - 1]
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED xPosition
                                               /\ UNCHANGED yPosition
                                          ELSE /\ IF  PositionInBounds(xPosition[self], yPosition[self] - 1)
                                                     /\ NoOtherRoverCollision(xPosition[self], yPosition[self] - 1, xPosition, yPosition)
                                                     /\ ~ThereIsObstacleColision
                                                     THEN /\ yPosition' = [yPosition EXCEPT ![self] = yPosition[self] - 1]
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED yPosition
                                               /\ UNCHANGED xPosition
              /\ pc' = [pc EXCEPT ![self] = "Mission"]
              /\ UNCHANGED orientation

Rover(self) == Mission(self) \/ Rotate(self) \/ Move(self)

Next == (\E self \in 1..NROVERS: Rover(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat Jan 25 21:27:02 CET 2020 by jesusmarin
\* Created Fri Jan 24 23:47:12 CET 2020 by jesusmarin
