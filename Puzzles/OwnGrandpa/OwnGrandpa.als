/*
 * An Alloy model of the song "I Am My Own Grandpa"
 * by Dwight B. Latham and Moe Jaffe
 *
 * The challenge is to produce a man who is his own grandfather
 * without resorting to incest or time travel.  Executing the predicate
 * "ownGrandpa" will demonstrate how such a thing can occur.
 *
 * The full song lyrics, which describe an isomorophic solution,
 * are included at the end of this file.
 *
 * model author: D. Jackson
 * modified: A. Cunha, N. Macedo
 */
abstract sig Person {
    father : lone Man,
    mother : lone Woman
}

sig Man extends Person {
    wife : lone Woman 
}
sig Woman extends Person {
    husband : lone Man 
}

fact {
    no p:Person | p in p.^(mother+father)   // Biology
    wife = ∼husband                         // Terminology
    no (wife+husband) & ^(mother+father)    // SocialConvention
    Person in                               // NoSolitary
        Person.(mother+father+∼mother+∼father+wife+husband) 
}

run {} for exactly 2 Man, exactly 2 Woman