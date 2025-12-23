module BBP_System

// --- GENERAL DOMAIN ENTITIES ---
sig GeoPoint {}

sig Path {
    starting_point: one GeoPoint,
    ending_point: one GeoPoint
}

fact starting_point_diff_ending_point { 
    all p: Path | p.starting_point != p.ending_point 
}


// --- DOMAIN HIERARCHIES ---

sig DateTime {}

sig Ride {
    trip_path: one Path,
    starting_datetime: one DateTime,
    ending_datetime: one DateTime
}

fact starting_datetime_not_ending_datetime {
    all t: Ride | t.starting_datetime != t.ending_datetime
}

sig User {
    user_trips: set Ride
}

// Constraint: a ride belongs to exactly one user
fact no_shared_trips {
    all r: Ride | one user_trips.r
}

sig Email {}

sig RegisteredUser extends User {
    email_address: one Email
}


// Constraint: One email per account
fact single_mail_single_account { 
    all e: Email | one email_address.e 
}

// enum listing all Activity states(see 2.1.3, Activity Lifecycle)
enum ActivityStatus {
    START,
    ROUTE_DEF,	// Route definition
    ON,             		// Ogoning
    MON_ON,         	// Monitored ongoing
    PAUSE,          	// Paused
    WAIT_CONF,      	// Waiting detections confirmation
    WAIT_RAT,       	// Waiting rating
    WEAT_ENR,       	// Waether enrichment
    COMPLETED       	// completed
}

sig Activity extends Ride { 
    var act_status : one ActivityStatus
}

// --- activity constraints
fact activity_only_to_registered_user {
	all a : Activity | user_trips.a in RegisteredUser
}
 
fact ride_to_normal_users { 
	all r: Ride | r in Ride-Activity implies user_trips.r in User-RegisteredUser 
}

// --- ACTIVITY LIFECYCLE ---

fact init_activity_state {
	all a : Activity | a.act_status = ROUTE_DEF
}

pred do_nothing_activity {
	act_status' = act_status
}

pred start_activity [a : Activity] {
    	a.act_status =  ROUTE_DEF
    	all ac : Activity-a | ac.act_status' = ac.act_status
    	a.act_status' = ON
}

pred start_monitored_activity [a : Activity] {
    	a.act_status =  ROUTE_DEF
    	all ac : Activity-a | ac.act_status' = ac.act_status
   	a.act_status' = MON_ON
}

pred stop_activity [a : Activity] {
    	a.act_status in ON+MON_ON
    	all ac : Activity-a | ac.act_status' = ac.act_status
    	a.act_status' = PAUSE
}

pred  resume_activity [a : Activity] {
    		a.act_status = PAUSE
    		all ac : Activity-a | ac.act_status' = ac.act_status
		a.act_status' in ON+MON_ON
}

// these two factes are needed to keep the activity consistent with the choice of normal or monitored after PAUSE state
fact resume_activity_constraint_1 {
	all a : Activity | always (
		a.act_status = ON implies historically (a.act_status != MON_ON)
	)
}
fact resume_activity_constraint_2 {
	all a : Activity | always (
		a.act_status = MON_ON implies historically (a.act_status != ON)
	)
}

pred terminate_monitored_activity [a : Activity] {
    	a.act_status = MON_ON
    	all ac : Activity-a | ac.act_status' = ac.act_status
    	a.act_status' = WAIT_CONF
}

pred rate_activity [a : Activity] {
    	a.act_status in ON+WAIT_CONF
    	all ac : Activity-a | ac.act_status' = ac.act_status
    	a.act_status' = WAIT_RAT
}

pred get_weather_info [a : Activity] {
    	a.act_status = WAIT_RAT
    	all ac : Activity-a | ac.act_status' = ac.act_status
    	a.act_status' = WEAT_ENR
}

pred complete_activity [a : Activity] {
    	a.act_status in WEAT_ENR+WAIT_RAT
    	all ac : Activity-a | ac.act_status' = ac.act_status
    	a.act_status' = COMPLETED
}

// ensures that once an activity reaches the COMPLTED state, it will remain forever in it
fact final_activity_state_stability  {
	all a : Activity | always (a.act_status = COMPLETED implies always a.act_status = COMPLETED)
}

fact valid_traces {
	always (
		do_nothing_activity or
		( some a : Activity | start_activity[a] ) or
		( some a : Activity | start_monitored_activity[a] ) or
		( some a : Activity | stop_activity[a] ) or
		( some a : Activity | resume_activity[a] ) or
		( some a : Activity | terminate_monitored_activity[a] ) or
		( some a : Activity | rate_activity[a] ) or
		( some a : Activity | get_weather_info[a] ) or
		( some a : Activity | complete_activity[a] )
	)	
}

pred showActivityLifecycle {
	// just to make the model instance more readable
	no User-RegisteredUser
	no Activity-Ride
	------------------------------
	one Path
	one Activity
	one RegisteredUser
	eventually ( some a : Activity | a.act_status = COMPLETED )	
}

//run showActivityLifecycle

pred showActivityLifecycleWithPause {
	// just to make the model instance more readable
	no User-RegisteredUser
	no Activity-Ride
	------------------------------
	one Path
	one Activity
	one RegisteredUser
	eventually ( some a : Activity | a.act_status = COMPLETED )	
	not (some a : Activity | a.act_status = COMPLETED) until (some a : Activity | a.act_status = PAUSE)
}

//run showActivityLifecycleWithPause

pred showActivityLifecycleWithWeatherEnrichment {
	// just to make the model instance more readable
	no User-RegisteredUser
	no Activity-Ride
	------------------------------
	one Path
	one Activity
	one RegisteredUser
	eventually ( some a : Activity | a.act_status = COMPLETED )	
	not (some a : Activity | a.act_status = COMPLETED) until (some a : Activity | a.act_status = WEAT_ENR)
}

//run showActivityLifecycleWithWeatherEnrichment

// --- REPORT LIFECYCLE --

enum ReportStatus { Pending, Confirmed, Discarded }

sig Report {
    //Solo i RegisteredUser possono essere autori
    author: one RegisteredUser, 
    refersTo: one Path,
    var report_status: one ReportStatus 
}

//Initial State
fact Init {
    all r: Report | r.report_status = Pending
}

//Once Confirmed or Discarded, it stays that way
fact Stability {
    always (all r: Report | r.report_status = Confirmed implies always r.report_status = Confirmed)
    always (all r: Report | r.report_status = Discarded implies always r.report_status = Discarded)
}

// PART 4: PREDICATES 

pred confirmReport [r: Report] {
    r.report_status = Pending
    r.report_status' = Confirmed
    all r2: Report - r | r2.report_status' = r2.report_status
}

pred discardReport [r: Report] {
    r.report_status = Pending
    r.report_status' = Discarded
    all r2: Report - r | r2.report_status' = r2.report_status
}

pred doNothing {
    report_status' = report_status
}

fact Traces {
    always (
        doNothing or
        (some r: Report | confirmReport[r]) or
        (some r: Report | discardReport[r])
    )
}

--------------------------------------------------------
// PART 5: EXECUTION COMMANDS for commands 
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
 	// Scope Reduction : We focus on a single actor and report for clarity	
	one RegisteredUser
	one Report

	 // Temporal Goal : The system must eventually reach a Confirmed state
	eventually ( some r : Report | r . report_status = Confirmed )
}


run showUserDistinction for 4
//run showDataLifecycle for 4
