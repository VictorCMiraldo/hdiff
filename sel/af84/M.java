/*
 * Copyright 2012-2017 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.springframework.boot.autoconfigure.jms.activemq;

import javax.jms.ConnectionFactory;
import javax.jms.JMSException;

import org.apache.activemq.ActiveMQConnectionFactory;
import org.apache.activemq.pool.PooledConnectionFactory;
import org.junit.Test;

import org.springframework.boot.autoconfigure.AutoConfigurations;
import org.springframework.boot.autoconfigure.jms.JmsAutoConfiguration;
import org.springframework.boot.test.context.ApplicationContextTester;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.mockingDetails;

/**
 * Tests for {@link ActiveMQAutoConfiguration}
 *
 * @author Andy Wilkinson
 * @author Aurélien Leboulanger
 * @author Stephane Nicoll
 */
public class ActiveMQAutoConfigurationTests {

	private final ApplicationContextTester context = new ApplicationContextTester()
			.withConfiguration(AutoConfigurations.of(ActiveMQAutoConfiguration.class,
					JmsAutoConfiguration.class));

	@Test
	public void brokerIsEmbeddedByDefault() {
		this.context.withUserConfiguration(EmptyConfiguration.class).run((loaded) -> {
			assertThat(loaded).getBean(ConnectionFactory.class)
					.isInstanceOf(ActiveMQConnectionFactory.class);
			assertThat(loaded.getBean(ActiveMQConnectionFactory.class).getBrokerURL())
					.isEqualTo("vm://localhost?broker.persistent=false");
		});
	}

	@Test
	public void configurationBacksOffWhenCustomConnectionFactoryExists() {
		this.context.withUserConfiguration(CustomConnectionFactoryConfiguration.class)
				.run((loaded) -> assertThat(
						mockingDetails(loaded.getBean(ConnectionFactory.class)).isMock())
								.isTrue());
	}

	@Test
	public void defaultsConnectionFactoryAreApplied() {
		this.context.withUserConfiguration(EmptyConfiguration.class)
				.withPropertyValues("spring.activemq.pool.enabled=false").run((loaded) -> {
			assertThat(loaded.getBeansOfType(ActiveMQConnectionFactory.class)).hasSize(1);
			ActiveMQConnectionFactory connectionFactory = loaded.getBean(
					ActiveMQConnectionFactory.class);
			ActiveMQConnectionFactory defaultFactory = new ActiveMQConnectionFactory(
					"vm://localhost?broker.persistent=false");
			assertThat(connectionFactory.getUserName()).isEqualTo(
					defaultFactory.getUserName());
			assertThat(connectionFactory.getPassword()).isEqualTo(
					defaultFactory.getPassword());
			assertThat(connectionFactory.getCloseTimeout()).isEqualTo(
					defaultFactory.getCloseTimeout());
			assertThat(connectionFactory.isNonBlockingRedelivery()).isEqualTo(
					defaultFactory.isNonBlockingRedelivery());
			assertThat(connectionFactory.getSendTimeout()).isEqualTo(
					defaultFactory.getSendTimeout());
			assertThat(connectionFactory.isTrustAllPackages()).isEqualTo(
					defaultFactory.isTrustAllPackages());
			assertThat(connectionFactory.getTrustedPackages()).containsExactly(
					defaultFactory.getTrustedPackages().toArray(new String[] {}));
		});
	}

	@Test
	public void customConnectionFactoryAreApplied() {
		this.context.withUserConfiguration(EmptyConfiguration.class)
				.withPropertyValues("spring.activemq.pool.enabled=false",
				"spring.activemq.brokerUrl=vm://localhost?useJmx=false&broker.persistent=false",
				"spring.activemq.user=foo",
				"spring.activemq.password=bar",
				"spring.activemq.closeTimeout=500",
				"spring.activemq.nonBlockingRedelivery=true",
				"spring.activemq.sendTimeout=1000",
				"spring.activemq.packages.trust-all=false",
				"spring.activemq.packages.trusted=com.example.acme").run((loaded) -> {
			assertThat(loaded.getBeansOfType(ActiveMQConnectionFactory.class)).hasSize(1);
			ActiveMQConnectionFactory connectionFactory = loaded.getBean(
					ActiveMQConnectionFactory.class);
			assertThat(connectionFactory.getUserName()).isEqualTo("foo");
			assertThat(connectionFactory.getPassword()).isEqualTo("bar");
			assertThat(connectionFactory.getCloseTimeout()).isEqualTo(500);
			assertThat(connectionFactory.isNonBlockingRedelivery()).isEqualTo(true);
			assertThat(connectionFactory.getSendTimeout()).isEqualTo(1000);
			assertThat(connectionFactory.isTrustAllPackages()).isFalse();
			assertThat(connectionFactory.getTrustedPackages()).containsExactly(
					"com.example.acme");
		});
	}

	@Test
	public void defaultsPooledConnectionFactoryAreApplied() {
		this.context.withUserConfiguration(EmptyConfiguration.class)
				.withPropertyValues("spring.activemq.pool.enabled=true").run((loaded) -> {
			assertThat(loaded.getBeansOfType(PooledConnectionFactory.class)).hasSize(1);
			PooledConnectionFactory connectionFactory = loaded.getBean(
					PooledConnectionFactory.class);
			PooledConnectionFactory defaultFactory = new PooledConnectionFactory();
			assertThat(connectionFactory.isBlockIfSessionPoolIsFull()).isEqualTo(
					defaultFactory.isBlockIfSessionPoolIsFull());
			assertThat(connectionFactory.getBlockIfSessionPoolIsFullTimeout()).isEqualTo(
					defaultFactory.getBlockIfSessionPoolIsFullTimeout());
			assertThat(connectionFactory.isCreateConnectionOnStartup()).isEqualTo(
					defaultFactory.isCreateConnectionOnStartup());
			assertThat(connectionFactory.getExpiryTimeout()).isEqualTo(
					defaultFactory.getExpiryTimeout());
			assertThat(connectionFactory.getIdleTimeout()).isEqualTo(
					defaultFactory.getIdleTimeout());
			assertThat(connectionFactory.getMaxConnections()).isEqualTo(
					defaultFactory.getMaxConnections());
			assertThat(connectionFactory.getMaximumActiveSessionPerConnection()).isEqualTo(
					defaultFactory.getMaximumActiveSessionPerConnection());
			assertThat(connectionFactory.isReconnectOnException()).isEqualTo(
					defaultFactory.isReconnectOnException());
			assertThat(connectionFactory.getTimeBetweenExpirationCheckMillis()).isEqualTo(
					defaultFactory.getTimeBetweenExpirationCheckMillis());
			assertThat(connectionFactory.isUseAnonymousProducers()).isEqualTo(
					defaultFactory.isUseAnonymousProducers());
		});
	}

	@Test
	public void customPooledConnectionFactoryAreApplied() {
		this.context.withUserConfiguration(EmptyConfiguration.class)
				.withPropertyValues("spring.activemq.pool.enabled=true",
				"spring.activemq.pool.blockIfFull=false",
				"spring.activemq.pool.blockIfFullTimeout=64",
				"spring.activemq.pool.createConnectionOnStartup=false",
				"spring.activemq.pool.expiryTimeout=4096",
				"spring.activemq.pool.idleTimeout=512",
				"spring.activemq.pool.maxConnections=256",
				"spring.activemq.pool.maximumActiveSessionPerConnection=1024",
				"spring.activemq.pool.reconnectOnException=false",
				"spring.activemq.pool.timeBetweenExpirationCheck=2048",
				"spring.activemq.pool.useAnonymousProducers=false").run((loaded) -> {
			assertThat(loaded.getBeansOfType(PooledConnectionFactory.class)).hasSize(1);
			PooledConnectionFactory connectionFactory = loaded.getBean(
					PooledConnectionFactory.class);
			assertThat(connectionFactory.isBlockIfSessionPoolIsFull()).isEqualTo(false);
			assertThat(connectionFactory.getBlockIfSessionPoolIsFullTimeout()).isEqualTo(64);
			assertThat(connectionFactory.isCreateConnectionOnStartup()).isEqualTo(false);
			assertThat(connectionFactory.getExpiryTimeout()).isEqualTo(4096);
			assertThat(connectionFactory.getIdleTimeout()).isEqualTo(512);
			assertThat(connectionFactory.getMaxConnections()).isEqualTo(256);
			assertThat(connectionFactory.getMaximumActiveSessionPerConnection())
					.isEqualTo(1024);
			assertThat(connectionFactory.isReconnectOnException()).isEqualTo(false);
			assertThat(connectionFactory.getTimeBetweenExpirationCheckMillis())
					.isEqualTo(2048);
			assertThat(connectionFactory.isUseAnonymousProducers()).isEqualTo(false);
		});
	}

	@Test
	public void pooledConnectionFactoryConfiguration() throws JMSException {
		this.context.withUserConfiguration(EmptyConfiguration.class)
				.withPropertyValues("spring.activemq.pool.enabled:true").run((loaded) -> {
					ConnectionFactory factory = loaded.getBean(ConnectionFactory.class);
					assertThat(factory).isInstanceOf(PooledConnectionFactory.class);
					loaded.getSourceApplicationContext().close();
					assertThat(factory.createConnection()).isNull();
				});
	}

	@Configuration
	static class EmptyConfiguration {

	}

	@Configuration
	static class CustomConnectionFactoryConfiguration {

		@Bean
		public ConnectionFactory connectionFactory() {
			return mock(ConnectionFactory.class);
		}

	}

	@Configuration
	static class CustomizerConfiguration {

		@Bean
		public ActiveMQConnectionFactoryCustomizer activeMQConnectionFactoryCustomizer() {
			return factory -> {
				factory.setBrokerURL(
						"vm://localhost?useJmx=false&broker.persistent=false");
				factory.setUserName("foobar");
			};
		}
	}

}
