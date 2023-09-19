// Copyright 2023 RisingWave Labs
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::path::Path;

use anyhow::{anyhow, Result};

use crate::GrafanaConfig;
pub struct GrafanaGen;

impl GrafanaGen {
    pub fn gen_custom_ini(&self, config: &GrafanaConfig) -> String {
        let grafana_host = &config.listen_address;
        let grafana_port = config.port;

        format!(
            r#"# --- THIS FILE IS AUTO GENERATED BY RISEDEV ---
[server]
http_addr = {grafana_host}
http_port = {grafana_port}

[users]
default_theme = light

[feature_toggles]
enable = traceToMetrics

[auth.anonymous]
enabled = true
org_role = Admin
    "#
        )
    }

    /// `risedev-prometheus.yml`
    pub fn gen_prometheus_datasource_yml(&self, config: &GrafanaConfig) -> Result<String> {
        let provide_prometheus = config.provide_prometheus.as_ref().unwrap();
        if provide_prometheus.len() != 1 {
            return Err(anyhow!(
                "expect 1 prometheus nodes, found {}",
                provide_prometheus.len()
            ));
        }
        let prometheus = &provide_prometheus[0];
        let prometheus_host = &prometheus.address;
        let prometheus_port = &prometheus.port;

        let yml = format!(
            r#"# --- THIS FILE IS AUTO GENERATED BY RISEDEV ---
apiVersion: 1
deleteDatasources:
  - name: risedev-prometheus
datasources:
  - name: risedev-prometheus
    type: prometheus
    access: proxy
    url: http://{prometheus_host}:{prometheus_port}
    withCredentials: false
    isDefault: true
    tlsAuth: false
    tlsAuthWithCACert: false
    version: 1
    editable: true
    "#,
        );
        Ok(yml)
    }

    /// `risedev-tempo.yml`
    pub fn gen_tempo_datasource_yml(&self, config: &GrafanaConfig) -> Result<String> {
        let provide_tempo = config.provide_tempo.as_ref().unwrap();
        if provide_tempo.len() != 1 {
            return Err(anyhow!(
                "expect 1 tempo nodes, found {}",
                provide_tempo.len()
            ));
        }
        let tempo = &provide_tempo[0];
        let tempo_host = &tempo.address;
        let tempo_port = &tempo.port;

        let yml = format!(
            r#"# --- THIS FILE IS AUTO GENERATED BY RISEDEV ---
apiVersion: 1
deleteDatasources:
  - name: risedev-tempo
datasources:
  - name: risedev-tempo
    type: tempo
    url: http://{tempo_host}:{tempo_port}
    jsonData:
      spanBar:
        type: None
    editable: true
    "#,
        );
        Ok(yml)
    }

    /// `grafana-risedev-dashboard.yml`
    pub fn gen_dashboard_yml(
        &self,
        config: &GrafanaConfig,
        generate_path: impl AsRef<Path>,
        grafana_read_path: impl AsRef<Path>,
    ) -> Result<String> {
        let provide_prometheus = config.provide_prometheus.as_ref().unwrap();
        if provide_prometheus.len() != 1 {
            return Err(anyhow!(
                "expect 1 prometheus nodes, found {}",
                provide_prometheus.len()
            ));
        };

        let filenames = [
            "risingwave-user-dashboard.json",
            "risingwave-dev-dashboard.json",
            "risingwave-traces.json", // TODO: generate this
        ];
        let generate_path = generate_path.as_ref();
        for filename in filenames {
            let from = Path::new("grafana").join(filename);
            let to = Path::new(generate_path).join(filename);
            std::fs::copy(from, to)?;
        }
        let grafana_read_path = grafana_read_path.as_ref();
        let dashboard_path_str = grafana_read_path
            .to_str()
            .ok_or_else(|| anyhow!("invalid string"))?;

        let yml = format!(
            r#"# --- THIS FILE IS AUTO GENERATED BY RISEDEV ---
apiVersion: 1

providers:
  - name: 'risingwave-grafana'
    orgId: 1
    folder: ''
    folderUid: ''
    type: file
    disableDeletion: false
    updateIntervalSeconds: 1
    allowUiUpdates: true
    options:
      path: {dashboard_path_str}
      foldersFromFilesStructure: false
    "#,
        );
        Ok(yml)
    }

    pub fn gen_s3_dashboard_yml(
        &self,
        config: &GrafanaConfig,
        prefix_config: impl AsRef<Path>,
    ) -> Result<String> {
        let provide_prometheus = config.provide_prometheus.as_ref().unwrap();
        if provide_prometheus.len() != 1 {
            return Err(anyhow!(
                "expect 1 prometheus nodes, found {}",
                provide_prometheus.len()
            ));
        };

        let prefix_config = prefix_config.as_ref();
        let s3_dashboard_path = Path::new(&prefix_config)
            .join("aws-s3.json")
            .to_string_lossy()
            .to_string();
        let yml = format!(
            r#"# --- THIS FILE IS AUTO GENERATED BY RISEDEV ---
apiVersion: 1

providers:
  - name: 's3-grafana'
    orgId: 1
    folder: ''
    folderUid: ''
    type: file
    disableDeletion: false
    updateIntervalSeconds: 60
    allowUiUpdates: true
    options:
      path: {s3_dashboard_path}
      foldersFromFilesStructure: false
    "#,
        );
        Ok(yml)
    }
}
