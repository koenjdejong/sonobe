use ark_ff::PrimeField;

pub const MAX_ACTIONS: usize = 8;
pub const MAX_GOODS: usize = 8;

pub const FIELDS_PER_ORDER: usize = 3 + 7 * MAX_ACTIONS + 3 * MAX_GOODS;

pub const ACTION_LOAD: u64 = 1;
pub const ACTION_UNLOAD: u64 = 2;
pub const ACTION_WAYPOINT: u64 = 3;

type ID = u64;
type ACTIVE = bool;

#[derive(Clone, Debug)]
pub struct Location { 
    pub id: ID, 
    pub longitude: u64, 
    pub latitude: u64 
}

#[derive(Clone, Debug)]
pub struct Action {
    pub id: ID,
    pub active: ACTIVE,
    pub location: Location,
    pub start_time: u64,
    pub end_time: u64,
    pub action_type: u64,
}

#[derive(Clone, Debug)]
pub struct Good {
    pub id: ID,
    pub active: ACTIVE, 
    pub weight: u64, 
    pub quantity: u64,
}

#[derive(Clone, Debug)]
pub struct Vehicle { 
    pub id: ID, 
    pub capacity: u64 
}

#[derive(Clone, Debug)]
pub struct TransportOrder {
    pub id: ID,
    pub active: ACTIVE,
    pub vehicle: Vehicle,
    pub actions: [Action; MAX_ACTIONS],
    pub goods: [Good; MAX_GOODS],
}

impl TransportOrder {
    pub fn flatten(&self) -> Vec<u64> {
        let mut v = Vec::with_capacity(FIELDS_PER_ORDER);
        v.push(self.id);
        v.push(self.active as u64);
        v.push(self.vehicle.id);
        v.push(self.vehicle.capacity);
        for a in &self.actions {
            v.push(a.id);
            v.push(a.active as u64);
            v.push(a.action_type);
            v.push(a.start_time);
            v.push(a.end_time);
            v.push(a.location.id);
            v.push(a.location.latitude);
            v.push(a.location.longitude);
        }
        for g in &self.goods {
            v.push(g.id);
            v.push(g.active as u64);
            v.push(g.quantity);
            v.push(g.weight);
        }
        debug_assert_eq!(v.len(), FIELDS_PER_ORDER);
        v
    }

    pub fn flatten_field<F: PrimeField>(&self) -> Vec<F> {
        self.flatten().into_iter().map(F::from).collect()
    }
}
