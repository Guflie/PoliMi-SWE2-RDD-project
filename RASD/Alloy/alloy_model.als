module BBP_System

--------------------------------------------------------
PART 1: DOMAIN MODEL
--------------------------------------------------------

sig GeoPoint {}

sig Path {
    starting_point: one GeoPoint,
    ending_point: one GeoPoint
}

fact starting_point_diff_ending_point { 
    all p: Path | p.starting_point != p.ending_point 
}

sig DateTime {}

sig Trip {
    trip_path: one Path,
    starting_datetime: one DateTime,
    ending_datetime: one DateTime
}

fact starting_datetime_not_ending_datetime {
    all t: Trip | t.starting_datetime != t.ending_datetime
}

--------------------------------------------------------
PART 2: USER HIERARCHY 
--------------------------------------------------------

sig User {
    user_trips: set Trip
}

//A trip belongs to exactly one user
fact no_shared_trips {
    all t: Trip | one user_trips.t
}

sig Email {}

// "RegisteredUser" estende User. Solo loro possono avere email e fare report.
sig RegisteredUser extends User {
    email_address: one Email
}

// Constraint: One email per account
fact single_mail_single_account { 
    all e: Email | one email_address.e 
}

--------------------------------------------------------
PART 3: DATA GOVERNANCE LIFECYCLE 
--------------------------------------------------------

enum ReportStatus { Pending, Confirmed, Discarded }

sig Report {
    //Solo i RegisteredUser possono essere autori
    author: one RegisteredUser, 
    refersTo: one Path,
    var status: one ReportStatus 
}

//Initial State
fact Init {
    all r: Report | r.status = Pending
}

//Once Confirmed or Discarded, it stays that way
fact Stability {
    always (all r: Report | r.status = Confirmed implies always r.status = Confirmed)
    always (all r: Report | r.status = Discarded implies always r.status = Discarded)
}

--------------------------------------------------------
PART 4: PREDICATES 
--------------------------------------------------------

pred confirmReport [r: Report] {
    r.status = Pending
    r.status' = Confirmed
    all r2: Report - r | r2.status' = r2.status
}

pred discardReport [r: Report] {
    r.status = Pending
    r.status' = Discarded
    all r2: Report - r | r2.status' = r2.status
}

pred doNothing {
    status' = status
}

fact Traces {
    always (
        doNothing or
        (some r: Report | confirmReport[r]) or
        (some r: Report | discardReport[r])
    )
}

--------------------------------------------------------
PART 5: EXECUTION COMMANDS 
--------------------------------------------------------

// SCENARIO 1: Differenza tra User generico e RegisteredUser
pred showUserDistinction {
    // Cerchiamo un mondo dove esiste almeno un utente non registrato
    some u: User | u not in RegisteredUser
    // E un utente registrato
    some RegisteredUser
    // E un report (che apparterrà per forza al registrato)
    some Report
}

// SCENARIO 2: Ciclo di vita del dato (Lifecycle)
pred showDataLifecycle {
    one RegisteredUser
    one Report
    // Il report diventa confermato nel tempo
    eventually (some r: Report | r.status = Confirmed)
}

run showUserDistinction for 4
run showDataLifecycle for 4
