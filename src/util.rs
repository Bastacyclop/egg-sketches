use egg::*;
use memory_stats::memory_stats;

pub fn grow_egraph_until<L, A, S>(
  search_name: &str,
  egraph: EGraph<L, A>,
  rules: &[Rewrite<L, A>], 
  mut satisfied: S
) -> EGraph<L, A>
where S: FnMut(&mut Runner<L, A>) -> bool + 'static,
      L: Language, A: Analysis<L>, A: Default
{
  let search_name_hook = search_name.to_owned();
  let runner = egg::Runner::default()
      .with_scheduler(egg::SimpleScheduler)
      .with_iter_limit(100)
      .with_node_limit(100_000_000)
      .with_time_limit(std::time::Duration::from_secs(5 * 60))
      .with_hook(move |runner| {
        let mut out_of_memory = false;
        // hook 0 <- nothing
        // iteration 0
        // hook 1 <- #0 size etc after iteration 0 + memory after iteration 0
        if let Some(it) = runner.iterations.last() {
          out_of_memory = iteration_stats(&search_name_hook, it, runner.iterations.len());
        }

        if satisfied(runner) {
          Err(String::from("Satisfied"))
        } else if out_of_memory {
          Err(String::from("Out of Memory"))
        } else {
          Ok(())
        }
      })
      .with_egraph(egraph)
      .run(&rules[..]);
  iteration_stats(search_name, runner.iterations.last().unwrap(), runner.iterations.len());
  runner.print_report();
  runner.egraph
}

// search name,
// iteration number,
// physical memory,
// virtual memory,
// e-graph nodes,
// e-graph classes,
// applied rules,
// total time,
// hook time,
// search time,
// apply time,
// rebuild time
fn iteration_stats(search_name: &str, it: &egg::Iteration<()>, it_number: usize) -> bool {
  let memory = memory_stats().expect("could not get current memory usage");
  let out_of_memory = memory.virtual_mem > 8_000_000_000;
  let found = match &it.stop_reason {
      Some(egg::StopReason::Other(s)) => s == "Satisfied",
      _ => false,
  };
  eprintln!("{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}",
      search_name,
      it_number,
      memory.physical_mem,
      memory.virtual_mem,
      it.egraph_nodes,
      it.egraph_classes,
      it.applied.iter().map(|(_, &n)| n).sum::<usize>(),
      it.total_time,
      it.hook_time,
      it.search_time,
      it.apply_time,
      it.rebuild_time,
      found);
  out_of_memory
}