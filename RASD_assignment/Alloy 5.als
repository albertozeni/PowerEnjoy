open util/boolean
open util/integer

sig Coordinates{
	latitude : Int,
	longitude : Int
}

fact No2SafeAreasInOneLocation{
	//two safe areas cannot have the same coordinates
	no s1, s2 : SafeArea | s1.position = s2.position and s1 != s2
}

sig SafeArea{
	position: Coordinates,
	parkedCar : set Car
}

sig SpecialParkingArea extends SafeArea{
	numPlugs : Int,
	carsInCharge : set Car
}
{
	numPlugs > 0
}

fact PlugNumberConstraint{
	//the number of cars parked in the same special parking
	//areas are equal or less thenumber of plugs
	all s1: SpecialParkingArea | #(s1.carsInCharge) <= s1.numPlugs
}

sig LicensePlate{}
fact LicensePlateBelongsToACar{
	all l1 : LicensePlate | one c1: Car | l1=c1.licensePlate
}
sig Car{
	position : Coordinates,
	maxPassengers: Int,
	licensePlate : LicensePlate,
	inCharge : Bool,
	reserved : Bool,
	Parked : Bool,
	inUse : Bool,
	locked : Bool,
	lowBattery : Bool
}
{
	maxPassengers=4
}
fact UniqueLicensePlatesForCars {
	//every car has a unique license plate to identify it
	no disj c1,c2 : Car | c1.licensePlate = c2.licensePlate
}


fact CarsInUseIfTheyAreInARide{
	//the attribute InUse of the car is true only if they are present
	//in a ride when we analyze the system
	all c1: Car | one r1: Ride | c1.inUse.isTrue implies (r1.car = c1)
	all r1: Ride, c1: Car | (r1.car = c1) implies c1.inUse.isTrue 
}

fact ParkedCarsCannotBeInUse{
	//the cars that are parked cannot be indicated as in use
	all c1 : Car | c1.Parked.isTrue implies c1.inUse.isFalse
}

fact OnlyParkedCarsAreLocked{
	//only the cars that are parked are Locked
	all c1 : Car | c1.Parked.isTrue implies c1.locked.isTrue
	all c1 : Car | c1.inUse.isTrue implies c1.locked.isFalse
}

fact CarsAlwaysHaveACurrentState{
	//every car has one boolean assigned as true, this ensure consistency
	all c1 : Car | c1.inCharge.isTrue or c1.Parked.isTrue or c1.inUse.isTrue
}

fact CarsInChargeAreParked{
	//all the cars that are in charge are signed as parked cars 
	all c1 : Car | c1.inCharge.isTrue implies c1.Parked.isTrue
}

fact CarsInUseAreNotInChargeNorParked{
	//if a car is in use it cannot be neither in charge nor parked
	all c1 : Car | c1.inUse.isTrue implies (c1.inCharge.isFalse and c1.Parked.isFalse)
}

fact ACarIsInSafeAreaIfItsPositionIsCorrect{
	//a car is parked in a safe area if and only if it's coordinates are the same as the safearea ones
	all c1 : Car, s1 : SafeArea | c1 in s1.parkedCar iff (c1.position = s1.position and c1.Parked.isTrue)
}

fact CarsAreInOnlyOneArea{
	//each car cannot be in multiple safeareas simultaneously
	no disj s1,s2 : SafeArea | #(s1.parkedCar & s2.parkedCar) > 0
	no disj s1,s2 : SpecialParkingArea | #(s1.carsInCharge & s2.carsInCharge) > 0
}

fact CarsInChargeAreParkedInSpecialParkingAreas{
	//the cars that are in charge are exclusively parked in special parking areas
	all c1: Car | one s1: SpecialParkingArea | c1.inCharge.isTrue implies (c1 in s1.carsInCharge and c1 in s1.parkedCar)
	all c1 : Car | one s1: SpecialParkingArea | c1 in s1.carsInCharge implies c1.inCharge.isTrue
}

fact OperatorsCannotUseReservedCars{
	//an operator cannot use a reserved car
	all c1: Car | no sr: SpecialRide | c1.reserved.isTrue and sr.car = c1 
}

abstract sig Person{
	drivingLicense: DrivingLicense,
	SSN: Int
}

sig DrivingLicense{
}

sig User extends Person{
	accountBalance: Int,
	debt:Int,
}
{
	accountBalance=0 implies debt>=0
	accountBalance>0 implies debt=0
	accountBalance>=0
}

fact DrivingLicensesBelongToSomeone{
	//every driving license as an owner
	all d1 : DrivingLicense | one p1: Person | p1.drivingLicense = d1
}

fact UsersCannotHaveTheSameSSNOrDrivingLicense{
	//each user as an unique SSN and Driving License
	no u1,u2 : User| u1.SSN=u2.SSN and u1!=u2
	no u1, u2 : User | u1.drivingLicense = u2.drivingLicense and u1 != u2
}


sig Operator extends Person{
}
{}

fact OperatorsCannotHaveTheSameSSNOrDrivingLicense{
	//each operator as an unique SSN and Driving License
	no o1,o2 : Operator| o1.SSN=o2.SSN and o1!=o2
	no o1, o2 : Operator | o1.drivingLicense = o2.drivingLicense and o1 != o2
}

//we are modeling time in time slots of an hour of a single day

abstract sig Ride{
	startTime: Int,
	startPosition: Coordinates,
	car: Car
}
{
	startTime>=0 startTime <=23
}

fact NoRidesCanBeDoneWithTheSameCarInTheSameMoment{
	//each ride has an unique car
	no disj r1, r2 : Ride | r1.car = r2.car
}

sig PaidRide extends Ride{
	costPerMinute: Int,
	totalCost: Int,
	reservation: Reservation,
	passengers: Int
}
{
	passengers>=0 passengers<=3
	totalCost>=costPerMinute
	costPerMinute=1
}

fact AllPaidRidesStartInASafeArea{
	//all paid rides starts in a safe area, because a reservation can be done
	//only if a car is in a safe area
	all r1 : PaidRide | one s1 : SafeArea | r1.startPosition=s1.position
}

fact NoRidesCanBeDoneInTheSameMomentByTheSameUser{
	//a user can do only one ride at a time
	no disj r1, r2 : PaidRide | r1.reservation.user = r2.reservation.user
}

fact NoRidesCanBeDoneInTheSameMomentByTheSameOperator{
	//an operator can do only one ride at a time
	no disj r1, r2 : SpecialRide | r1.operator = r2.operator
}

fact NoReservationsCanBeDoneInTheSameMomentByTheSameUser{
	//a user can do only one reservation at a time
	no disj r1, r2 : Reservation | r1.user = r2.user
}

fact UsersCannotBeOperatorsAtTheSameTime{
	//an operator can be a user, but it needs a separate account
	//with this fact we ensure that someone cannot drive a car as both at the same time
	all u: User, o:Operator | no pr: PaidRide, sr: SpecialRide | u.SSN = o.SSN and pr.reservation.user = u and sr.operator = o 
}

sig SpecialRide extends Ride{
	operator: Operator
}

sig Reservation{
	startTime: Int,
	unlockTime: lone Int,
	user: User,
	car: Car
}
{
	unlockTime>=startTime
	unlockTime<=startTime+1
	startTime>=0 startTime<=22
}

fact UnlockTimeOfReservationIsTheStartTimeOfThePaidRide{
	//the moment when the car is unlocked corrisponds with
	//the moment in which the ride starts
	all p: PaidRide | p.startTime = p.reservation.unlockTime
}

fact ReservationsAndPaidRidesHaveTheSameCar{
	//reservation and car have the same car as attribute
	all r1: Reservation,  p1: PaidRide | p1.reservation = r1 iff p1.car = r1.car
}

fact ACarHasAReservationIfItIsReserved{
	//the boolean attribute in car that says the car is reserved it's true
	//if and only if the car is inside a reservation
	all c1: Car | one r1:Reservation | c1.reserved.isTrue implies r1.car = c1
	all r1: Reservation | r1.car.reserved.isTrue
}

fact NoReservationCanBeDoneByAUserWithLowBalance{
	//a user that has low balance cannot make a reservation
	//this is done to prevent that users make debits
	all r1 : Reservation | r1.user.accountBalance>=2
}

fact NoReservationCanBeDoneByAUserWithADebt{
	//the users with a debt cannot make any reservation
	no r1 : Reservation | r1.user.debt > 0
}

fact NoReservationCanHaveTheSameRide{
	//each ride corrispond to an unique reservation
	no disj p1,p2 : PaidRide | p1.reservation=p2.reservation
}
fact NoReservationCanHaveTheSameCar{
	//each car corrispond to an unique reservation
	no disj r1,r2 : Reservation | r1.car = r2.car
}

fact NoReservationCanBeDoneOnACarParkedInAnUnsafeArea{
		//all reservations are done only for cars parked in safe areas
		no r: Reservation | r.car.Parked.isTrue and not r.car in SafeArea.parkedCar
}

fact NoReservationCanBeDoneOnACarWithLowBattery{
	//a car that has low battery cannot be reserved
	all c: Car | c.lowBattery.isTrue and c.inUse.isFalse implies c.reserved.isFalse
}
pred ThereAreNoCarReservedWithLowBattery{

}

/*
pred ActiveReservation{
	some r1 : Reservation | no p1 : PaidRide | p1.reservation=r1
}

run ActiveReservation
*/
/*
pred CarsCanBeInUnsafeAreas{
	some c1: Car | c1.Parked.isTrue and not c1 in SafeArea.parkedCar
}

run CarsCanBeInUnsafeAreas*/ //NON DEVONO ESSERE PRENOTATE, fatto!


/*pred Prova{
	some c1: Car | c1.inUse.isTrue
	some r1: Ride | r1.car.inUse.isTrue
	some r: Reservation | no p1 : PaidRide | p1.reservation=r
//	one c2: Car | c2.lowBattery.isTrue and c2.reserved.isTrue and c2.inUse.isFalse no instance found!! ok
}

run Prova*/
assert NoReservedCarIsInAnUnsafeArea{
	//ensures that every reserved car is in a safe
	no c1: Car | all s1: SafeArea | c1.reserved.isTrue and c1.Parked.isTrue and c1.position!=s1.position
}
assert NoUserWithLowBalanceHasAReservation{
	//ensure that only users with wnough money can do reservations
	no r1: Reservation | r1.user.accountBalance<2
}
assert NoUserCanDoMultipleReservations{
	//enusures each user can do only one reservation at a time
	no disj r1,r2 : Reservation | r1.user=r2.user
}
assert NoCarIsPickedUpInAnUnsafeAreaForAPaidRide{
	//ensures that all the cars picked up for the paid rides were in safe areas
	no r1: PaidRide | all s1: SafeArea | r1.startPosition!=s1.position
}
assert NoCarInChargeIsNotInASpecialParkingArea{
	//ensures that all the cars that are in charge are in special parking areas
	no c1: Car | all s1: SpecialParkingArea | c1.inCharge.isTrue and c1.Parked.isTrue and c1.position!=s1.position
}

pred show(){}
//check NoReservedCarIsInAnUnsafeArea
//check NoUserWithLowBalanceHasAReservation
//check NoUserCanDoMultipleReservations
//check NoCarIsPickedUpInAnUnsafeAreaForAPaidRide
//check NoCarInChargeIsNotInASpecialParkingArea

run show
//Ho messo: le macchine non possono essere prenotate se sono in unsafe area
// l'unlock time deve coincidere allo start time della ride
// low battery
// una macchina non può essere prenotata se ha low battery
//utenti con debiti non possono fare reservation
