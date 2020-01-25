# TLA+ spec: Rover

Spec of multiple rover robots moving on a grid of given size.
The rovers can make the following actions:
* Rotate to North, West, East, South
* Move forward

The spec verify:
* There is no collision between different rovers
* A rover can't move out of the grid
* Any position of the grid can contain an obstacle, if it contains an obstacle rover can't move to that position

This spec has been tested up to 20 rovers, using TLC.
