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