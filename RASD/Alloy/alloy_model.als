sig GeoPoint { }

some sig Path {
	starting_point : one GeoPoint
	, ending_point : one GeoPoint
	/** I think the list of points is irrelevant for the model checking**/
}


fact starting_point_diff_ending_point { 
	all p : Path | p.starting_point != p.ending_point
}

// ----------------------------------------------------------------------------------------------------------------------------------------------------------------------
sig DateTime { }

some sig Trip {
	trip_path : one Path
	, starting_datetime : one DateTime
	, ending_datetime : one DateTime
}

/** todo: should we define a temporal contraint, e.g. starting_datetime < ending_datetime? Maybe isn't that much relevant **/
// a trip can't have the starting_datetime = ending_datetime
fact starting_datetime_not_ending_datetime {
	all t : Trip | t.starting_datetime != t.ending_datetime
}


// ----------------------------------------------------------------------------------------------------------------------------------------------------------------------
some sig User { 
	user_trips : some Trip
}

// a trip must be "owned" only by one user
fact no_shared_trips {
	all t  : Trip | one user_trips.t
}

// ----------------------------------------------------------------------------------------------------------------------------------------------------------------------

sig Email { }
sig Password { }
sig Name { }
sig Surname { }
sig BirthDate { }


some sig RegisteredUser in User{
	email_address: one Email
}

// one email couldn't be used for more account
fact single_mail_single_account { 
	all e : Email | one email_address.e
}



run example { }
