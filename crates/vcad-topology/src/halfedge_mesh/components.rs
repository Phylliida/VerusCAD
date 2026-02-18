use std::collections::{HashSet, VecDeque};

use super::Mesh;
impl Mesh {
    pub fn component_count(&self) -> usize {
        self.half_edge_components().len()
    }

    pub fn euler_characteristics_per_component(&self) -> Vec<isize> {
        #[cfg(feature = "verus-proofs")]
        {
            if let Some(chis) =
                crate::runtime_halfedge_mesh_refinement::euler_characteristics_per_component_constructive(self)
            {
                return chis;
            }
        }

        self.euler_characteristics_per_component_raw()
    }

    pub(super) fn euler_characteristics_per_component_raw(&self) -> Vec<isize> {
        let mut out = Vec::new();
        for component in self.half_edge_components() {
            let mut vertices = HashSet::new();
            let mut edges = HashSet::new();
            let mut faces = HashSet::new();
            for h in component {
                let he = &self.half_edges[h];
                vertices.insert(he.vertex);
                edges.insert(he.edge);
                faces.insert(he.face);
            }
            out.push(vertices.len() as isize - edges.len() as isize + faces.len() as isize);
        }
        out
    }

    pub fn check_euler_formula_closed_components(&self) -> bool {
        #[cfg(feature = "verus-proofs")]
        {
            if let Some(w) =
                crate::runtime_halfedge_mesh_refinement::check_euler_formula_closed_components_constructive(self)
            {
                return w.api_ok;
            }
        }

        self.check_euler_formula_closed_components_raw()
    }

    pub(super) fn check_euler_formula_closed_components_raw(&self) -> bool {
        let chis = self.euler_characteristics_per_component_raw();
        !chis.is_empty() && chis.into_iter().all(|chi| chi == 2)
    }
    fn half_edge_components(&self) -> Vec<Vec<usize>> {
        let mut components = Vec::new();
        if self.half_edges.is_empty() {
            return components;
        }

        let mut visited = vec![false; self.half_edges.len()];
        for start in 0..self.half_edges.len() {
            if visited[start] {
                continue;
            }

            let mut queue = VecDeque::new();
            let mut component = Vec::new();
            queue.push_back(start);
            visited[start] = true;

            while let Some(h) = queue.pop_front() {
                component.push(h);
                let he = &self.half_edges[h];
                let neighbors = [he.twin, he.next, he.prev];
                for n in neighbors {
                    if !visited[n] {
                        visited[n] = true;
                        queue.push_back(n);
                    }
                }
            }

            components.push(component);
        }

        components
    }
}
