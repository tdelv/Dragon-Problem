#lang forge

sig Dragon {}

abstract sig Color {}
one sig Blue extends Color {}
one sig Black extends Color {}

sig World {
    eyeColors : set Dragon -> Color
}

